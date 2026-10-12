/* Vendored from 250tech/nextact-offer-parser (src/util.js + src/parse.js).
   Self-hosted deliberately: the tool claims client-side processing, and a CDN
   request would still be a session-correlated request.
   Re-vendor after any parser change — this is a COPY, not a live import. */
// Shared helpers. No dependencies — everything here must be able to run in a browser later.

/** Deterministic PRNG so corpus + eval are reproducible across runs. */
function rng(seed) {
  let s = seed >>> 0;
  return () => {
    s = (s * 1664525 + 1013904223) >>> 0;
    return s / 4294967296;
  };
}

const pick = (r, arr) => arr[Math.floor(r() * arr.length)];
const int = (r, lo, hi) => lo + Math.floor(r() * (hi - lo + 1));

// Sentinel standing in for a period that must NOT end a sentence.
const DOT = String.fromCharCode(1);

/**
 * Sentence segmentation that does not break on the abbreviations and decimals
 * that actually appear in offer letters (Inc., U.S., $185,000.00, No. 4).
 */
function sentences(text) {
  const guarded = text
    .replace(/\b(Inc|Corp|Ltd|LLC|Co|No|Approx|Dept|Mr|Mrs|Ms|Dr|St|vs|Jr|Sr)\./gi, (m) => m.slice(0, -1) + DOT)
    .replace(/\b([A-Za-z])\.(?=\s?[A-Za-z]\.)/g, '$1' + DOT)
    .replace(/(\d)\.(\d)/g, '$1' + DOT + '$2');

  return guarded
    // Newlines are hard boundaries: offer letters are frequently line-oriented
    // tables ("Annual Base    $185,000") with no terminal punctuation at all.
    .split(/(?<=[.!?])\s+|\n+/)
    .map((s) => s.split(DOT).join('.').trim())
    .filter(Boolean);
}

const MONTHS = {
  january: 1, february: 2, march: 3, april: 4, may: 5, june: 6,
  july: 7, august: 8, september: 9, october: 10, november: 11, december: 12,
  jan: 1, feb: 2, mar: 3, apr: 4, jun: 6, jul: 7, aug: 8, sep: 9, sept: 9, oct: 10, nov: 11, dec: 12,
};

const MONTH_NAMES = [
  'January', 'February', 'March', 'April', 'May', 'June',
  'July', 'August', 'September', 'October', 'November', 'December',
];

const iso = (y, m, d) => `${y}-${String(m).padStart(2, '0')}-${String(d).padStart(2, '0')}`;

/**
 * Find every date literal in a string, with its character offset.
 * Handles: "March 14, 2026" · "14 March 2026" · "3/14/2026" · "2026-03-14" · "March 14th, 2026"
 */
function findDateLiterals(text) {
  const out = [];
  const push = (raw, index, y, m, d) => {
    if (m < 1 || m > 12 || d < 1 || d > 31) return;
    out.push({ raw, index, iso: iso(y, m, d) });
  };

  const monthAlt = Object.keys(MONTHS).join('|');
  const reMDY = new RegExp(`\\b(${monthAlt})\\.?\\s+(\\d{1,2})(?:st|nd|rd|th)?,?\\s+(\\d{4})\\b`, 'gi');
  const reDMY = new RegExp(`\\b(\\d{1,2})(?:st|nd|rd|th)?\\s+(?:of\\s+)?(${monthAlt})\\.?,?\\s+(\\d{4})\\b`, 'gi');
  const reNum = /\b(\d{1,2})\/(\d{1,2})\/(\d{4})\b/g;   // US convention: M/D/Y
  const reISO = /\b(\d{4})-(\d{2})-(\d{2})\b/g;

  let m;
  while ((m = reMDY.exec(text))) push(m[0], m.index, +m[3], MONTHS[m[1].toLowerCase()], +m[2]);
  while ((m = reDMY.exec(text))) push(m[0], m.index, +m[3], MONTHS[m[2].toLowerCase()], +m[1]);
  while ((m = reNum.exec(text))) push(m[0], m.index, +m[3], +m[1], +m[2]);
  while ((m = reISO.exec(text))) push(m[0], m.index, +m[1], +m[2], +m[3]);

  // De-duplicate overlapping matches, keeping the longest literal at each position.
  out.sort((a, b) => a.index - b.index || b.raw.length - a.raw.length);
  return out.filter((d, i) => !out.slice(0, i).some((p) => d.index < p.index + p.raw.length));
}

const CURRENCY = { $: 'USD', '£': 'GBP', '€': 'EUR', '₹': 'INR' };

/**
 * Monetary amounts with offsets. Handles US (1,234.56) and European (1.234,56)
 * grouping, symbol- and ISO-code-prefixed forms, and "120k" shorthand.
 * Bare numbers are deliberately NOT money.
 */
function findMoney(text) {
  const out = [];
  const re = /(?:(USD|GBP|EUR|CAD|INR)\s*)?([$£€₹])?\s?(\d{1,3}(?:[.,]\d{3})*(?:[.,]\d{1,2})?|\d+(?:\.\d+)?)\s*(k\b|K\b)?/g;
  let m;
  while ((m = re.exec(text))) {
    const [raw, code, sym, num, k] = m;
    if (!code && !sym && !k) continue;
    if (!/\d/.test(num)) continue;

    // European format: a comma with exactly two trailing digits, alongside dot grouping.
    const euro = /,\d{2}$/.test(num) && num.includes('.');
    const normalized = euro ? num.replace(/\./g, '').replace(',', '.') : num.replace(/,/g, '');

    let value = parseFloat(normalized);
    if (k) value *= 1000;
    if (!Number.isFinite(value)) continue;

    const lead = raw.length - raw.trimStart().length;
    out.push({ raw: raw.trim(), index: m.index + lead, value, currency: code || CURRENCY[sym] || 'USD' });
  }
  return out;
}

/**
 * PDF text extractors split words mid-token: "th ree (3) working days", "start d ate",
 * "hir e-on bonus", "Progr am". Every word-boundary regex fails silently on these, and
 * a synthetic corpus of clean prose will never surface it.
 *
 * Rather than repair the text (guessing where words belong is lossy), we build a
 * whitespace-free VIEW of it plus an index map back to the original. Cue phrases are
 * matched against the view; positions are translated back so value extraction and
 * proximity assignment still operate on the real string.
 */
function despace(text) {
  let flat = '';
  const map = [];
  for (let i = 0; i < text.length; i++) {
    if (/\s/.test(text[i])) continue;
    flat += text[i].toLowerCase();
    map.push(i);
  }
  return { flat, map };
}

/**
 * Rewrite a cue regex to match against a despaced view: drop whitespace tokens,
 * literal spaces, and word boundaries (which don't exist once spaces are gone).
 */
function despaceRe(re) {
  const src = re.source
    .replace(/\\s[+*?]?/g, '')
    .replace(/\\b/g, '')
    .replace(/ /g, '');
  return new RegExp(src, 'i');
}

/** DocuSign / Adobe form-field names that leak into the extracted text stream. */
function stripFormArtifacts(text) {
  return text.replace(
    /\b(?:dateSigned|fullName|signature|initial|title|company|email|text|checkbox|name)\d+\b/gi,
    ' '
  );
}

const isWeekend = (d) => d.getUTCDay() === 0 || d.getUTCDay() === 6;

/** Add N days to an ISO date; `businessOnly` skips Saturdays and Sundays. */
function addDays(isoDate, n, businessOnly = false) {
  const d = new Date(isoDate + 'T00:00:00Z');
  if (!businessOnly) {
    d.setUTCDate(d.getUTCDate() + n);
  } else {
    let left = n;
    while (left > 0) {
      d.setUTCDate(d.getUTCDate() + 1);
      if (!isWeekend(d)) left--;
    }
  }
  return d.toISOString().slice(0, 10);
}

function findPercents(text) {
  const out = [];
  // Both "15%" and the spelled-out "15 percent" — UK/formal letters use the latter.
  const re = /(\d{1,3}(?:\.\d+)?)\s?(?:%|per\s?cent\b)/gi;
  let m;
  while ((m = re.exec(text))) out.push({ raw: m[0], index: m.index, value: parseFloat(m[1]) });
  return out;
}

// Offer-letter field extractor — v0.2
//
// CONTRACT (from the settled /offer spec):
//   · Operates on TEXT only. PDF/DOCX/clipboard extraction is a separate, swappable layer.
//   · Every returned value carries its SOURCE SENTENCE for the confirmation screen.
//   · ABSTENTION IS A FIRST-CLASS OUTCOME. No cue, or two roles too close together →
//     {abstain: true} rather than a guess. A wrong response deadline is the catastrophic
//     error; a missing one is merely unhelpful.
//   · The parser NEVER concludes. It reports what the document says.
//
// v0.2 changes, all driven by 4 real offer letters (see Notion, 2026-08-06):
//   1. Two-tier cue matching — clean text matches precisely; dirty PDF text ("start d ate",
//      "hir e-on bonus") recovers via a despaced view at reduced confidence.
//   2. Relative deadlines — most real letters say "valid for three (3) working days from
//      the date of this letter" rather than naming a date. Resolved against the letterhead
//      date with business-day math.
//   3. Missing cue phrases from real letters + relocation_bonus as its own field.
//   4. DocuSign/Adobe form-field artifacts stripped.

const MONEY_CUES = {
  base_salary: [
    [/\bannual(?:ized)?\s+base\s+salary\b/i, 1.0],
    [/\bbase\s+salary\b/i, 0.95],
    [/\bannual\s+base\b/i, 0.95],
    [/\bannual\s+salary\b/i, 0.9],
    [/\bsalary\s+(?:will\s+be|of|is|shall\s+be)\b/i, 0.85],
    [/\bsalary\s*:/i, 0.9],
    [/\bcompensation\s+for\s+this\s+role\b[^.]{0,40}\bset\s+at\b/i, 0.9],
    [/\bbase\s+is\b/i, 0.85],
  ],
  signon_bonus: [
    [/\bone-time\s+signing\s+bonus\b/i, 1.0],
    [/\bsign(?:ing)?[-\s]?on\s+(?:award|bonus|payment)\b/i, 0.95],
    [/\bsigning\s+bonus\b/i, 0.95],
    [/\bsign[-\s]?on\s*:/i, 0.9],
    [/\bsign[-\s]?on\b/i, 0.8],
    [/\bwelcome\s+payment\b/i, 0.9],
    [/\bstarting\s+bonus\b/i, 0.9],
    // ── v0.2, from real letters ──
    [/\bhire[-\s]?on\s+bonus\b/i, 1.0],
    [/\bhiring\s+bonus\b/i, 0.95],
  ],
  // v0.2b: a bonus is not always a percentage. Real letters state it as a dollar cap
  // ("Eligibility for a discretionary bonus up to $X annually"), which the percent-only
  // bonus handling could never capture.
  bonus_amount: [
    [/\bdiscretionary\s+bonus\b/i, 0.95],
    [/\bbonus\s+up\s+to\b/i, 0.9],
    [/\bannual\s+bonus\b/i, 0.85],
    // Deliberately NOT "bonus in the amount of" — that's a carrier phrase, not a bonus
    // type. It sits closer to the money than "hire-on bonus" does, so proximity would
    // hand it the value and mis-attribute every sign-on bonus.
  ],
  // v0.2: real letters carry this as a distinct term with its own repayment clawback.
  relocation_bonus: [
    [/\brelocation\s+bonus\b/i, 1.0],
    [/\brelocation\s+(?:allowance|payment|package)\b/i, 0.95],
  ],
};

const PERCENT_CUES = {
  bonus_target_pct: [
    [/\bannual\s+target\s+bonus\b/i, 1.0],
    [/\btarget\s+bonus\b/i, 0.95],
    [/\bbonus\s+target\b/i, 0.95],
    [/\btarget\s+award\s+of\b/i, 0.9],
    [/\bbonus\s+eligibility\s+targeted\s+at\b/i, 0.9],
    [/\btarget\s+of\b/i, 0.7],
    // ── v0.2, from real letters ──
    [/\bbonus\s+of\s+up\s+to\b/i, 0.95],
    [/\bbonus\s+program\b[^.]{0,60}\beligible\b/i, 0.85],
    [/\beligible,?\s+at\b/i, 0.8],
  ],
};

const DATE_CUES = {
  response_deadline: [
    [/\bno\s+later\s+than\b/i, 0.95],
    [/\b(?:offer\s+)?expires\s+on\b/i, 1.0],
    [/\bremain\s+open\s+for\s+your\s+acceptance\s+until\b/i, 1.0],
    [/\bindicate\s+your\s+acceptance\b/i, 0.9],
    [/\bsigning\s+and\s+returning\s+this\s+letter\b/i, 0.9],
    [/\bneed\s+an\s+answer\s+by\b/i, 0.9],
    [/\baccept(?:ance)?\s+by\b/i, 0.85],
    [/\bconfirm\s+your\s+decision\b/i, 0.95],
    [/\bcountersigned\b/i, 0.95],
    [/\bsign\s+and\s+return\b/i, 0.9],
    // v0.2b: "on or before" is NOT deadline-specific — real letters also use it for the
    // start date ("Your start date will be on or before X"). Scored high only when
    // acceptance language precedes it; the bare form sits BELOW start_date's 0.85 so a
    // start-date sentence wins outright instead of colliding into an abstention.
    [/(?:sign|return|accept|confirm)[^.]{0,60}\bon\s+or\s+before\b/i, 0.9],
    [/\bon\s+or\s+before\b/i, 0.65],
    // ── v0.2, from real letters ──
    [/\bsign\s+and\s+date\s+this\s+letter\b/i, 0.95],
    [/\bclose\s+of\s+business\s+on\b/i, 0.95],
    [/\bconfirm\s+your\s+acceptance\b/i, 0.9],
  ],
  start_date: [
    [/\banticipated\s+start\s+date\b/i, 1.0],
    [/\bstart\s+date\s+is\b/i, 1.0],
    [/\bstart\s+date\s+will\s+be\b/i, 1.0],
    [/\bwill\s+(?:start|begin)\s+on\b/i, 0.95],
    [/\bbegin\s+(?:work|employment)\s+on\b/i, 1.0],
    [/\bemployment\s+sh(?:all|ould)\s+commence\b/i, 1.0],
    [/\bcommence\s+employment\s+on\b/i, 1.0],
    [/\bfirst\s+day\b/i, 0.9],
    [/\bhoping\s+you\s+can\s+start\b/i, 0.9],
    [/\bwelcome\s+you\s+to\s+the\s+team\s+on\b/i, 0.95],
    [/\bin\s+the\s+door\b/i, 0.75],
    [/\bstart\s+date\b/i, 0.85],
    // Kept at 0.8 deliberately: "vesting commencement date" is a grant_date cue at 0.9,
    // so the MARGIN check makes an ambiguous "commencement" abstain rather than guess.
    [/\bcommence(?:ment)?\b/i, 0.8],
  ],
  grant_date: [
    [/\bgrant\s+date\b/i, 1.0],
    [/\bvesting\s+commencement\s+date\b/i, 0.9],
    [/\bapprove\s+grants\s+on\b/i, 0.9],
    [/\baward\s+date\b/i, 0.95],
  ],
  // Absorbs distractor dates so they aren't mis-filed as real deadlines.
  _superseded: [
    [/\bamends?\s+and\s+replaces\b/i, 1.0],
    [/\bcorrespondence\s+dated\b/i, 0.9],
    [/\bletter\s+dated\b/i, 0.85],
  ],
};

const EQUITY_PATTERNS = [
  /([\d,]{2,})\s+(?:restricted\s+stock\s+units|RSUs?)\b/i,
  /options?\s+to\s+purchase\s+([\d,]{2,})\s+shares/i,
  /granted\s+([\d,]{2,})\s+restricted\s+stock\s+units/i,
  /award\s+of\s+([\d,]{2,})\s+shares/i,          // v0.2: "RSU award of 12,000 shares"
  /([\d,]{2,})\s+(?:stock\s+)?options\b/i,
];

const MARGIN = 0.15;         // top role must beat runner-up by this, else abstain
const FLOOR = 0.6;           // minimum score to emit anything
const DIRTY_PENALTY = 0.85;  // confidence multiplier when only the despaced view matched

// Despaced variants are derived once, not per sentence.
const despacedCache = new WeakMap();
const dsr = (re) => {
  let v = despacedCache.get(re);
  if (!v) { v = despaceRe(re); despacedCache.set(re, v); }
  return v;
};

/**
 * Score cue phrases against a sentence. Tries the precise regex first; if that fails,
 * retries against a whitespace-free view so that PDF-mangled text still matches, at
 * reduced confidence (which surfaces in the UI as "check this").
 */
function scoreCues(sentence, table, flat) {
  const scores = {};
  for (const [field, cues] of Object.entries(table)) {
    let best = 0;
    let at = -1;
    for (const [re, w] of cues) {
      const m = re.exec(sentence);
      if (m) {
        if (w > best) { best = w; at = m.index; }
        continue;
      }
      const dm = dsr(re).exec(flat.flat);
      if (dm) {
        const w2 = w * DIRTY_PENALTY;
        if (w2 > best) { best = w2; at = flat.map[dm.index] ?? 0; }
      }
    }
    if (best > 0) scores[field] = { score: best, index: at };
  }
  return scores;
}

function decide(scores) {
  const ranked = Object.entries(scores).sort((a, b) => b[1].score - a[1].score);
  if (!ranked.length) return null;
  const [field, top] = ranked[0];
  if (top.score < FLOOR) return null;
  if (ranked[1] && top.score - ranked[1][1].score < MARGIN) return null;
  return { field, confidence: top.score, cueIndex: top.index };
}

/**
 * Assign a role to ONE date literal — not to the sentence it sits in.
 *
 * Scoring per sentence was a catastrophic bug: "You will start on April 1, 2026 if you
 * accept by March 14, 2026" gave both literals the same role, reporting the START DATE
 * as the response deadline. Two rules fix it:
 *
 *   1. A cue must PRECEDE the literal it describes. Offer letters overwhelmingly read
 *      "accept by X" / "start date is X" / "no later than X" — never the reverse. A date
 *      with no preceding cue ABSTAINS rather than borrowing a later cue's role.
 *   2. Among preceding cues, nearer ones win, via distance decay — then the usual margin
 *      check, so two comparable candidates abstain instead of guessing.
 */
function decideForLiteral(scores, litIndex) {
  const decay = (d) => 1 / (1 + d / 60);
  const ranked = Object.entries(scores)
    .filter(([, s]) => s.index <= litIndex)
    .map(([field, s]) => ({ field, effective: s.score * decay(litIndex - s.index), raw: s.score }))
    .sort((a, b) => b.effective - a.effective);

  if (!ranked.length) return null;                     // no preceding cue → abstain
  const top = ranked[0];
  if (top.raw < FLOOR) return null;
  if (ranked[1] && top.effective - ranked[1].effective < MARGIN * decay(0)) return null;
  return { field: top.field, confidence: top.raw };
}

function assignByProximity(literals, scores) {
  const cues = Object.entries(scores).map(([field, s]) => ({ field, ...s }));
  if (!cues.length) return [];
  return literals.map((lit) => {
    const preceding = cues.filter((c) => c.index <= lit.index);
    const pool = preceding.length ? preceding : cues;
    const chosen = pool.reduce((a, b) => {
      const da = Math.abs(lit.index - a.index);
      const db = Math.abs(lit.index - b.index);
      return db < da || (db === da && b.score > a.score) ? b : a;
    });
    return { literal: lit, field: chosen.field, confidence: chosen.score };
  });
}

const better = (a, b) => !a || b.confidence > a.confidence;

/**
 * v0.2 — relative deadlines. Most real letters express the response deadline as an
 * interval from the letterhead date rather than naming a date:
 *   "valid for three (3) working days from the date of this letter"
 *   "This offer expires two (2) days from the date of this letter."
 * The parenthetical digit in "three (3)" is reliably present, so we key on it.
 */
const REL_RE =
  /(?:valid\s+for|expires?|remain(?:s)?\s+open\s+for|open\s+for)\D{0,25}?(\d{1,2})\s*\)?\s*(working|business|calendar)?\s*days?\s+(?:from|of|after)\s+the\s+date\s+of\s+this\s+letter/i;

function findRelativeDeadline(text, flat, letterDate) {
  let m = REL_RE.exec(text);
  let dirty = false;
  if (!m) { m = dsr(REL_RE).exec(flat.flat); dirty = !!m; }
  if (!m || !letterDate) return null;

  const n = parseInt(m[1], 10);
  if (!Number.isFinite(n) || n < 1 || n > 90) return null;
  const business = /work|business/i.test(m[2] || '');

  return {
    role: 'response_deadline',
    iso: addDays(letterDate, n, business),
    raw: m[0].replace(/\s+/g, ' ').trim(),
    confidence: (business ? 0.85 : 0.9) * (dirty ? DIRTY_PENALTY : 1),
    anchor_provenance: 'relative-to-document-date',
    computed: { n, unit: business ? 'business days' : 'calendar days', from: letterDate },
  };
}

function parseOffer(rawText) {
  const text = stripFormArtifacts(rawText);

  const result = {
    fields: {
      base_salary: { abstain: true },
      signon_bonus: { abstain: true },
      bonus_amount: { abstain: true },
      relocation_bonus: { abstain: true },
      bonus_target_pct: { abstain: true },
      equity: { abstain: true },
    },
    dates: {},
    letterDate: null,
    notStated: [],
  };

  // The letterhead date anchors every relative deadline, so getting it wrong silently
  // moves the deadline. "First date literal in the document" was naive: a reference to a
  // prior letter, a footer timestamp, or a DocuSign stamp appearing earlier would hijack
  // the anchor. Observed failure: an April letter anchored to a referenced March date,
  // putting the computed deadline 41 days out.
  //
  // A real letterhead date sits ALONE on its own line near the top. We require that, and
  // reject lines that reference another document. If we can't identify one confidently we
  // return null, and no relative deadline is computed at all.
  const REFERENCE_LINE = /\b(?:letter|correspondence|agreement|memo|email)\s+(?:dated|of)\b|\bre:|\bref:|\bamends?\s+and\s+replaces\b|\bsigned\s+on\b/i;
  const lines = text.split('\n').slice(0, 40);

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i].trim();
    if (!line || REFERENCE_LINE.test(line)) continue;
    const lits = findDateLiterals(line);
    if (lits.length !== 1) continue;
    // The line must be essentially nothing but the date (allow a trailing comma/period).
    const residue = line.replace(lits[0].raw, '').replace(/[.,\s]/g, '');
    if (residue.length === 0) {
      result.letterDate = lits[0].iso;
      result.letterDateConfidence = 'dateline';
      break;
    }
  }

  // Fallback: first date NOT in a line referencing another document. Marked as weak so
  // the UI can require confirmation before any arithmetic is trusted.
  if (!result.letterDate) {
    for (const line of lines) {
      if (!line.trim() || REFERENCE_LINE.test(line)) continue;
      const lits = findDateLiterals(line);
      if (lits.length) {
        result.letterDate = lits[0].iso;
        result.letterDateConfidence = 'inferred';
        break;
      }
    }
  }

  const collected = [];

  for (const sentence of sentences(text)) {
    const flat = despace(sentence);

    const moneyScores = scoreCues(sentence, MONEY_CUES, flat);
    for (const { literal, field, confidence } of assignByProximity(findMoney(sentence), moneyScores)) {
      if (confidence < FLOOR) continue;
      const cand = { value: literal.value, currency: literal.currency, confidence, sentence };
      const cur = result.fields[field].abstain ? null : result.fields[field];
      if (better(cur, cand)) result.fields[field] = cand;
    }

    const pctScores = scoreCues(sentence, PERCENT_CUES, flat);
    for (const { literal, field, confidence } of assignByProximity(findPercents(sentence), pctScores)) {
      if (confidence < FLOOR) continue;
      const cand = { value: literal.value, confidence, sentence };
      const cur = result.fields[field].abstain ? null : result.fields[field];
      if (better(cur, cand)) result.fields[field] = cand;
    }

    for (const re of EQUITY_PATTERNS) {
      let eq = re.exec(sentence);
      let conf = 0.9;
      if (!eq) { eq = dsr(re).exec(flat.flat); if (eq) conf = 0.9 * DIRTY_PENALTY; }
      if (!eq) continue;
      const amount = parseInt(String(eq[1]).replace(/,/g, ''), 10);
      if (!Number.isFinite(amount) || amount < 10) continue;
      const type = /option/i.test(eq[0]) ? 'OPTION' : 'RSU';
      const cand = { type, amount, confidence: conf, sentence };
      const cur = result.fields.equity.abstain ? null : result.fields.equity;
      if (better(cur, cand)) result.fields.equity = cand;
      break;
    }

    const dateScores = scoreCues(sentence, DATE_CUES, flat);
    for (const lit of findDateLiterals(sentence)) {
      const verdict = decideForLiteral(dateScores, lit.index);
      if (!verdict || verdict.field === '_superseded') continue;
      collected.push({
        role: verdict.field, iso: lit.iso, raw: lit.raw,
        confidence: verdict.confidence, sentence,
        anchor_provenance: 'stated-in-document',
      });
    }
  }

  for (const d of collected) if (better(result.dates[d.role], d)) result.dates[d.role] = d;

  // Only fall back to a relative deadline if none was stated outright — AND only when the
  // anchor is a real dateline.
  //
  // The `inferred` anchor must never drive arithmetic. It was still doing so: a
  // benefits-effective date in the body was picked up as the letter date and a deadline
  // computed from it. A wrong anchor produces a confident, plausible, wrong deadline —
  // strictly worse than no deadline. When we only have an inferred anchor we say so and
  // let the user supply the letter date.
  if (!result.dates.response_deadline) {
    const hasRelativeLanguage = REL_RE.test(text) || dsr(REL_RE).test(despace(text).flat);
    if (hasRelativeLanguage && result.letterDateConfidence === 'dateline') {
      const rel = findRelativeDeadline(text, despace(text), result.letterDate);
      if (rel) result.dates.response_deadline = rel;
    } else if (hasRelativeLanguage) {
      result.needsLetterDate = true;   // UI must ask before anything is computed
    }
  }

  for (const [k, v] of Object.entries(result.fields)) if (v.abstain) result.notStated.push(k);
  for (const role of ['response_deadline', 'start_date', 'grant_date']) {
    if (!result.dates[role]) result.notStated.push(role);
  }

  return result;
}
