// ---------- status semantics: what a problem's statuses say, and how that compares to its expectation ----------
// Pure functions, no DOM: the page bundles this file (explore.rs) and the Node tests load it
// (tests/explore/status_semantics.test.mjs). The badge, the landing page, the namespace browser
// and the filters all read problems through `problemStatus`, so the vocabulary is the same
// everywhere.
//
// Stored codes. The database stores SZS-style codes per problem (`summary`, `statuses`): THM
// ("for every argument", or plainly "true" with no arguments), UNS ("for no argument"), SAT
// ("for some argument"), CSA ("false for some argument"), `contingent` (SAT and CSA), OPN and UNK.
// They are kept as stored; this file only interprets them.
//
// Facts. Each stored code is a fact about the problem P(x) over its argument carrier:
//   SAT: ∃x. P x  (s = true)        CSA: ∃x. ¬P x  (c = true)
//   THM: ¬∃x. ¬P x (c = false)      UNS: ¬∃x. P x  (s = false)      contingent: s and c
// plus whether the carrier is inhabited (e). A closed problem (arity 0) has one point, so e
// holds and P is simply true (s, ¬c) or false (¬s, c). For a problem with parameters e is assumed
// unless the facts refute it: THM and UNS together hold only over an empty carrier ("vacuous").
//
// Displayed codes depend on the arity, so the vocabulary is consistent:
//   no parameters:   THM  (Theorem: the statement is proved)
//                    CTH  (CounterTheorem: its negation is proved)
//   with parameters: TAU  (holds for every argument; stored THM)
//                    UNS  (holds for no argument)
//                    SAT  (holds for some argument; not known for all)
//                    CSA  (fails for some argument; not known for all)
//                    NOC  (NoConsequence: holds for some and fails for some; stored contingent)
//   either:          OPN  (open: nothing is established), UNK (unknown)
//
// Expectations (`problems.expect`) are compared by entailment, not by code equality: an
// expectation is a set of facts, and the problem's established facts either
//   contradict it    "contrary"   e.g. TAU established, UNS expected
//   leave it open    "weaker"     less information than expected, e.g. CSA established where UNS
//                                 is expected (CSA follows from UNS on an inhabited carrier, but
//                                 not conversely), or nothing established ("pending")
//   entail exactly   "match"
//   entail more      "stronger"   information that was not expected, e.g. TAU where only SAT is
//                                 expected, or anything established where OPN is expected
// A finding classified `error` overrides the outcome ("error"). Deprecated problems and problems
// carrying an `expected_open` marking (a metatheoretic reason, e.g. independence) keep their
// outcome but are left out of the landing page's attention lists (`attention`).

const STATUS_FACTS = Object.freeze({
  THM: { c: false }, UNS: { s: false }, SAT: { s: true }, CSA: { c: true },
  contingent: { s: true, c: true }, OPN: {}, UNK: {},
});
const STATUS_UNKNOWN = new Set(["OPN", "UNK"]);
// Expectation codes as the checker reads them (case-insensitive).
const STATUS_EXPECT_CODES = ["THM", "SAT", "UNS", "CSA", "OPN", "UNK", "contingent"];
function normExpect(e) {
  if (e == null || e === "") return null;
  return STATUS_EXPECT_CODES.find((c) => c.toLowerCase() === String(e).toLowerCase()) || String(e);
}

// The displayed codes, with what each says. `params` is whether the code is used for problems with
// parameters (true), without (false) or both (null).
const DISPLAY_CODES = Object.freeze({
  THM: { name: "Theorem", params: false, text: "proved (no parameters)" },
  CTH: { name: "CounterTheorem", params: false, text: "disproved: the negation is proved (no parameters)" },
  TAU: { name: "Tautology", params: true, text: "holds for every argument" },
  UNS: { name: "Unsatisfiable", params: true, text: "holds for no argument" },
  SAT: { name: "Satisfiable", params: true, text: "holds for some argument; not known for every one" },
  CSA: { name: "CounterSatisfiable", params: true, text: "fails for some argument; not known to fail for every one" },
  NOC: { name: "NoConsequence", params: true, text: "holds for some arguments and fails for others" },
  OPN: { name: "Open", params: null, text: "nothing is established yet" },
  UNK: { name: "Unknown", params: null, text: "unknown" },
  CON: { name: "Conflict", params: null, text: "the established statuses contradict each other" },
});
const DISPLAY_ORDER = ["THM", "CTH", "TAU", "UNS", "SAT", "CSA", "NOC", "OPN", "UNK", "CON"];

// Expectation outcomes, in the order of attention.
const OUTCOMES = Object.freeze({
  error: { label: "genuine error", text: "a finding classifies the refutation as a genuine error" },
  contrary: { label: "contrary to expectation", text: "the established statuses contradict the expected status" },
  weaker: { label: "less information than expected", text: "the expected status is not established yet; what is established is consistent with it" },
  stronger: { label: "more information than expected", text: "the established statuses entail the expected status and say more" },
  match: { label: "as expected", text: "the established statuses are exactly the expected status" },
  none: { label: "no expectation", text: "the problem has no expected status" },
});
const OUTCOME_ORDER = ["error", "contrary", "weaker", "stronger", "match", "none"];

// --- three-valued facts ---
function newFacts(arity) { return { s: null, c: null, e: arity === 0 ? true : null, point: arity === 0, conflict: false }; }
function setFact(k, key, v) {
  if (k[key] === null) { k[key] = v; return true; }
  if (k[key] !== v) k.conflict = true;
  return false;
}
// The consequences of the facts: S → E, C → E, E ∧ ¬C → S, E ∧ ¬S → C, ¬S ∧ ¬C → ¬E, and on a
// one-point carrier (no parameters) S ↔ ¬C.
function closeFacts(k) {
  for (let changed = true; changed && !k.conflict;) {
    changed = false;
    if (k.s === true || k.c === true) changed = setFact(k, "e", true) || changed;
    if (k.e === true && k.c === false) changed = setFact(k, "s", true) || changed;
    if (k.e === true && k.s === false) changed = setFact(k, "c", true) || changed;
    if (k.s === false && k.c === false) changed = setFact(k, "e", false) || changed;
    if (k.point && k.s !== null) changed = setFact(k, "c", !k.s) || changed;
    if (k.point && k.c !== null) changed = setFact(k, "s", !k.c) || changed;
  }
  return k;
}
// The facts of a list of stored codes. `assumeInhabited`: assume a carrier is inhabited unless
// the facts refute it (the reading of displayed codes).
function factsOf(codes, arity, assumeInhabited) {
  const k = newFacts(arity);
  for (const code of codes) {
    const f = STATUS_FACTS[code];
    if (!f) continue;
    if ("s" in f) setFact(k, "s", f.s);
    if ("c" in f) setFact(k, "c", f.c);
  }
  closeFacts(k);
  if (assumeInhabited && !k.conflict && k.e === null) { k.e = true; closeFacts(k); }
  return k;
}
function knownAny(k) { return k.s !== null || k.c !== null; }

// The displayed code of a fact state.
function displayOf(k, arity, summary) {
  if (k.conflict) return "CON";
  if (arity === 0) return k.s === true ? "THM" : k.s === false ? "CTH" : summary === "UNK" ? "UNK" : "OPN";
  if (k.e === false) return "TAU";   // vacuous: every and no argument; the title says so
  if (k.s === true && k.c === false) return "TAU";
  if (k.s === false && k.c === true) return "UNS";
  if (k.s === true && k.c === true) return "NOC";
  if (k.s === true) return "SAT";
  if (k.c === true) return "CSA";
  return summary === "UNK" ? "UNK" : "OPN";
}
// The displayed code an expectation stands for at this arity (THM expected of a problem with
// parameters is shown as TAU, UNS expected of a closed one as CTH).
function expectDisplay(expect, arity) {
  const e = normExpect(expect);
  if (!e) return null;
  if (!STATUS_FACTS[e]) return e;
  return displayOf(factsOf([e], arity, true), arity, e);
}

// Compare the established facts with an expectation (see the header).
function compareExpectation(k, expect, arity) {
  const e = normExpect(expect);
  if (!e) return "none";
  if (e === "OPN" || e === "UNK") return knownAny(k) ? "stronger" : "match";
  const f = STATUS_FACTS[e];
  if (!f) return "none";
  const req = Object.entries(f).filter(([key]) => key === "s" || key === "c");
  if (k.conflict) return "contrary";
  if (req.some(([key, v]) => k[key] === !v)) return "contrary";
  if (!req.every(([key, v]) => k[key] === v)) return "weaker";
  if (k.e === false) return "match";   // vacuous: the expectation holds, over an empty carrier
  const want = factsOf([e], arity, true);
  return ["s", "c"].some((key) => k[key] !== null && want[key] !== k[key]) ? "stronger" : "match";
}

// Everything the views need about one problem. `row`: { summary, arity, expect, established
// (codes), deprecated, finding, expectedOpen ({ reason, note }) }.
function problemStatus(row) {
  if (!row) return null;
  const arity = row.arity == null ? null : Number(row.arity);
  const summary = row.summary || "OPN";
  // established codes: an array, or a database row's group_concat (space- or comma-separated)
  const established = Array.isArray(row.established) ? row.established
    : typeof row.established === "string" ? row.established.split(/[\s,]+/).filter(Boolean) : [];
  const codes = established.length ? [...new Set([summary, ...established])] : [summary];
  const k = factsOf(codes, arity, true);
  const raw = factsOf(codes, arity, false);
  const code = displayOf(k, arity, summary);
  const expect = normExpect(row.expect);
  let outcome = row.finding === "error" ? "error" : compareExpectation(k, expect, arity);
  const pending = outcome === "weaker" && !knownAny(raw);
  const open = code === "OPN" || code === "UNK";
  const deprecated = row.deprecated || null;
  const expectedOpen = row.expectedOpen || (row.expected_open ? { reason: row.expected_open, note: row.expected_open_note || null } : null);
  return {
    code, stored: summary, codes, arity, closed: arity === 0, open, outcome, pending,
    expect, expectCode: expect ? expectDisplay(expect, arity) : null,
    vacuous: k.e === false && !k.conflict, conflict: k.conflict,
    deprecated, expectedOpen, finding: row.finding || null,
    attention: attentionOf({ code, outcome, open, deprecated, expectedOpen }),
  };
}

// Why a problem is (or is not) on the landing page's attention lists.
//   "contrary"  contradicts its expectation, or a genuine-error finding
//   "open"      nothing established (OPN/UNK)
//   "weaker"    less information than expected (something established, not the expectation)
//   "stronger"  information that was not expected
// A deprecated problem, or one with an `expected_open` marking that is still open, is "excluded"
// (with its reason): still listed on its own page, in the browser and under the filters.
function attentionOf(st) {
  if (st.deprecated) return { list: null, excluded: "deprecated" };
  if (st.expectedOpen && st.open) return { list: null, excluded: "expected-open" };
  if (st.outcome === "contrary" || st.outcome === "error") return { list: "contrary" };
  if (st.open) return { list: "open" };
  if (st.outcome === "weaker") return { list: "weaker" };
  if (st.outcome === "stronger") return { list: "stronger" };
  return { list: null };
}

// One-line explanation of a problem's status, for titles and screen readers.
function statusExplanation(st) {
  if (!st) return "";
  const d = DISPLAY_CODES[st.code];
  const parts = [`${st.code}${d ? " (" + d.name + ")" : ""}: ${d ? d.text : "status"}`];
  if (st.vacuous) parts.push("vacuous: holds for every and for no argument, so the argument carrier is empty");
  const shownStored = st.codes.filter((c) => c !== "OPN" || st.codes.length === 1);
  parts.push(`stored ${shownStored.join(", ")}`);
  if (st.arity != null) parts.push(st.arity === 0 ? "no parameters" : `${st.arity} parameter${st.arity === 1 ? "" : "s"}`);
  if (st.expect) parts.push(`expected ${st.expectCode}${st.expectCode !== st.expect ? " (stored " + st.expect + ")" : ""}`);
  parts.push(st.pending ? "less information than expected: nothing established yet" : OUTCOMES[st.outcome].label);
  if (st.deprecated) parts.push("deprecated" + (st.deprecated === "self" ? "" : ` (through its ${st.deprecated})`));
  if (st.expectedOpen) parts.push(`expected to stay open (${st.expectedOpen.reason})`);
  if (st.finding && st.finding !== "error") parts.push(`finding: ${st.finding}`);
  return parts.join("; ");
}

// The namespace tree of dotted names: { name, path, children: Map, problems: [] }. A problem
// whose name is also a prefix of others (a group and its members) sits at its own node.
function namespaceTree(names) {
  const root = { name: "", path: "", children: new Map(), items: [] };
  for (const n of names) {
    const parts = splitName(n);
    let node = root;
    for (let i = 0; i < parts.length - 1; i++) {
      const part = parts[i];
      if (!node.children.has(part)) node.children.set(part, { name: part, path: parts.slice(0, i + 1).join("."), children: new Map(), items: [] });
      node = node.children.get(part);
    }
    node.items.push(n);
  }
  return root;
}
// Dotted name components; «…» quotes and `/` (legacy silmaril ids) are kept inside a component.
function splitName(n) {
  const out = [];
  let cur = "", q = 0;
  for (const ch of String(n)) {
    if (ch === "«") q++;
    else if (ch === "»" && q) q--;
    if (ch === "." && !q) { out.push(cur); cur = ""; } else cur += ch;
  }
  out.push(cur);
  return out.filter((p, i, a) => p !== "" || a.length === 1);
}
// The node at a dotted path (or null).
function namespaceNode(root, path) {
  if (!path) return root;
  let node = root;
  for (const part of splitName(path)) { node = node.children.get(part); if (!node) return null; }
  return node;
}
// Every problem name under a node.
function namespaceItems(node) {
  const out = [...node.items];
  for (const c of node.children.values()) out.push(...namespaceItems(c));
  return out;
}

// A status filter: { codes: Set of displayed codes (empty: any), outcomes: Set (empty: any),
// attention: bool, hideExcluded: bool }.
function matchesFilter(st, f) {
  if (!st) return false;
  if (f.codes && f.codes.size && !f.codes.has(st.code)) return false;
  if (f.outcomes && f.outcomes.size && !f.outcomes.has(st.pending ? "pending" : st.outcome) && !f.outcomes.has(st.outcome)) return false;
  if (f.attention && !st.attention.list) return false;
  if (f.hideExcluded && st.attention.excluded) return false;
  return true;
}

const StatusSemantics = Object.freeze({
  STATUS_FACTS, DISPLAY_CODES, DISPLAY_ORDER, OUTCOMES, OUTCOME_ORDER,
  normExpect, factsOf, displayOf, expectDisplay, compareExpectation, problemStatus, attentionOf,
  statusExplanation, namespaceTree, namespaceNode, namespaceItems, splitName, matchesFilter,
});
if (typeof module !== "undefined" && module.exports) module.exports = StatusSemantics;
