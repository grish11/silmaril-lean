// Unit tests of the explorer's status semantics (src/project/explore/status.js): displayed codes by
// arity, expectation outcomes by entailment, the landing page's attention lists and exclusions,
// the status filter and the namespace tree.
//
//   node --test tools/silmaril-project/tests/explore/status_semantics.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const S = createRequire(import.meta.url)(path.join(here, "../../src/project/explore/status.js"));
const st = (row) => S.problemStatus(row);
const co = (row) => { const s = st(row); return `${s.code}/${s.outcome}`; };

test("closed problems read THM or CTH, whatever code is stored", () => {
  assert.equal(st({ summary: "THM", arity: 0 }).code, "THM");
  assert.equal(st({ summary: "SAT", arity: 0 }).code, "THM");
  assert.equal(st({ summary: "UNS", arity: 0 }).code, "CTH");
  assert.equal(st({ summary: "CSA", arity: 0 }).code, "CTH");
  assert.equal(st({ summary: "OPN", arity: 0 }).code, "OPN");
  assert.equal(st({ summary: "UNK", arity: 0 }).code, "UNK");
});

test("problems with parameters read TAU, UNS, SAT, CSA, NOC", () => {
  assert.equal(st({ summary: "THM", arity: 1 }).code, "TAU");
  assert.equal(st({ summary: "UNS", arity: 2 }).code, "UNS");
  assert.equal(st({ summary: "SAT", arity: 1 }).code, "SAT");
  assert.equal(st({ summary: "CSA", arity: 1 }).code, "CSA");
  assert.equal(st({ summary: "contingent", arity: 3 }).code, "NOC");
  // SAT and CSA established separately are NoConsequence too
  assert.equal(st({ summary: "SAT", arity: 1, established: ["SAT", "CSA"] }).code, "NOC");
  assert.equal(st({ summary: "OPN", arity: 4 }).code, "OPN");
});

test("THM and UNS together are vacuous (empty carrier), not a conflict", () => {
  const s = st({ summary: "THM", arity: 1, established: ["THM", "UNS"] });
  assert.equal(s.vacuous, true);
  assert.equal(s.conflict, false);
  assert.equal(s.outcome, "none");
  assert.equal(co({ summary: "THM", arity: 1, expect: "UNS", established: ["THM", "UNS"] }), "TAU/match");
  assert.equal(co({ summary: "THM", arity: 1, expect: "SAT", established: ["THM", "UNS"] }), "TAU/contrary");
});

test("SAT with UNS is a conflict", () => {
  const s = st({ summary: "SAT", arity: 1, established: ["SAT", "UNS"] });
  assert.equal(s.code, "CON");
  assert.equal(s.conflict, true);
});

test("expectations compare by entailment", () => {
  // the user's example: CSA where UNS is expected is less information, not the opposite
  assert.equal(co({ summary: "CSA", arity: 1, expect: "UNS", established: ["CSA"] }), "CSA/weaker");
  assert.equal(co({ summary: "SAT", arity: 1, expect: "THM", established: ["SAT"] }), "SAT/weaker");
  // contradictions
  assert.equal(co({ summary: "UNS", arity: 1, expect: "THM", established: ["UNS"] }), "UNS/contrary");
  assert.equal(co({ summary: "THM", arity: 0, expect: "UNS", established: ["THM", "SAT"] }), "THM/contrary");
  assert.equal(co({ summary: "contingent", arity: 1, expect: "THM", established: ["SAT", "CSA"] }), "NOC/contrary");
  assert.equal(co({ summary: "CSA", arity: 1, expect: "SAT" }), "CSA/weaker");
  // more than expected
  assert.equal(co({ summary: "THM", arity: 1, expect: "SAT", established: ["THM"] }), "TAU/stronger");
  assert.equal(co({ summary: "UNS", arity: 1, expect: "CSA", established: ["UNS"] }), "UNS/stronger");
  assert.equal(co({ summary: "contingent", arity: 1, expect: "sat", established: ["SAT", "CSA"] }), "NOC/stronger");
  // exactly as expected
  assert.equal(co({ summary: "THM", arity: 1, expect: "THM" }), "TAU/match");
  assert.equal(co({ summary: "contingent", arity: 1, expect: "contingent" }), "NOC/match");
  // closed problems: UNS and CSA say the same; THM and SAT say the same
  assert.equal(co({ summary: "UNS", arity: 0, expect: "CSA", established: ["UNS", "CSA"] }), "CTH/match");
  assert.equal(co({ summary: "UNS", arity: 0, expect: "CSA" }), "CTH/match");
  assert.equal(co({ summary: "CSA", arity: 0, expect: "UNS", established: ["CSA"] }), "CTH/match");
  assert.equal(co({ summary: "THM", arity: 0, expect: "SAT" }), "THM/match");
  // no expectation is neutral whatever the status
  assert.equal(co({ summary: "UNS", arity: 0 }), "CTH/none");
  // a genuine-error finding overrides
  assert.equal(co({ summary: "CSA", arity: 0, finding: "error" }), "CTH/error");
});

test("open problems: pending when something is expected, stronger when expected open but resolved", () => {
  const p = st({ summary: "OPN", arity: 0, expect: "THM" });
  assert.equal(p.outcome, "weaker");
  assert.equal(p.pending, true);
  assert.equal(st({ summary: "CSA", arity: 1, expect: "UNS" }).pending, false);
  assert.equal(co({ summary: "OPN", arity: 1, expect: "OPN" }), "OPN/match");
  assert.equal(co({ summary: "THM", arity: 0, expect: "OPN" }), "THM/stronger");
});

test("expected codes are shown in the arity's vocabulary", () => {
  assert.equal(st({ summary: "OPN", arity: 1, expect: "THM" }).expectCode, "TAU");
  assert.equal(st({ summary: "OPN", arity: 0, expect: "UNS" }).expectCode, "CTH");
  assert.equal(st({ summary: "OPN", arity: 0, expect: "CSA" }).expectCode, "CTH");
  assert.equal(st({ summary: "OPN", arity: 2, expect: "contingent" }).expectCode, "NOC");
  assert.equal(st({ summary: "OPN", arity: 2, expect: "OPN" }).expectCode, "OPN");
});

test("attention: contrary, open, weaker, stronger; deprecated and expected-open are excluded", () => {
  assert.equal(st({ summary: "UNS", arity: 1, expect: "THM" }).attention.list, "contrary");
  assert.equal(st({ summary: "CSA", arity: 0, finding: "error" }).attention.list, "contrary");
  assert.equal(st({ summary: "OPN", arity: 1 }).attention.list, "open");
  assert.equal(st({ summary: "OPN", arity: 1, expect: "OPN" }).attention.list, "open");   // a fixture expected open is still open
  assert.equal(st({ summary: "CSA", arity: 1, expect: "UNS" }).attention.list, "weaker");
  assert.equal(st({ summary: "THM", arity: 1, expect: "SAT" }).attention.list, "stronger");
  assert.equal(st({ summary: "THM", arity: 1, expect: "THM" }).attention.list, null);
  assert.equal(st({ summary: "UNS", arity: 0 }).attention.list, null);
  const dep = st({ summary: "contingent", arity: 1, expect: "THM", deprecated: "self" });
  assert.deepEqual(dep.attention, { list: null, excluded: "deprecated" });
  const meta = st({ summary: "OPN", arity: 0, expectedOpen: { reason: "consistency" } });
  assert.deepEqual(meta.attention, { list: null, excluded: "expected-open" });
  // a marking does not hide a problem once it is resolved
  assert.equal(st({ summary: "THM", arity: 0, expect: "OPN", expectedOpen: { reason: "independent" } }).attention.list, "stronger");
});

test("filters by displayed code, outcome, attention and exclusion", () => {
  const rows = [
    st({ summary: "THM", arity: 0 }), st({ summary: "UNS", arity: 0, expect: "CSA" }), st({ summary: "OPN", arity: 2 }),
    st({ summary: "CSA", arity: 1, expect: "UNS" }), st({ summary: "OPN", arity: 0, deprecated: "self" }),
  ];
  const f = (o) => rows.filter((s) => S.matchesFilter(s, o)).map((s) => s.code);
  assert.deepEqual(f({ codes: new Set(["CTH"]) }), ["CTH"]);
  assert.deepEqual(f({ codes: new Set(["OPN"]) }), ["OPN", "OPN"]);
  assert.deepEqual(f({ codes: new Set(["OPN"]), hideExcluded: true }), ["OPN"]);
  assert.deepEqual(f({ outcomes: new Set(["weaker"]) }), ["CSA"]);
  assert.deepEqual(f({ attention: true }), ["OPN", "CSA"]);
  assert.deepEqual(f({}), ["THM", "CTH", "OPN", "CSA", "OPN"]);
});

test("explanations name the code, the stored codes, the arity and the expectation", () => {
  const t = S.statusExplanation(st({ summary: "UNS", arity: 0, expect: "CSA", established: ["UNS", "CSA"] }));
  assert.match(t, /^CTH \(CounterTheorem\)/);
  assert.match(t, /stored UNS, CSA/);
  assert.match(t, /no parameters/);
  assert.match(t, /expected CTH \(stored CSA\)/);
  assert.match(t, /as expected/);
  assert.match(S.statusExplanation(st({ summary: "OPN", arity: 0, expect: "THM" })), /nothing established yet/);
});

test("namespace tree by dotted components, keeping «quoted» components whole", () => {
  assert.deepEqual(S.splitName("a.«b.c».d"), ["a", "«b.c»", "d"]);
  assert.deepEqual(S.splitName("x/y.z"), ["x/y", "z"]);
  const t = S.namespaceTree(["silmaril.all", "silmaril.selftest.open", "silmaril.selftest.languages.json_has_one",
    "silmaril.selftest.languages", "formats.catalogue.x"]);
  assert.deepEqual([...t.children.keys()], ["silmaril", "formats"]);
  const sel = S.namespaceNode(t, "silmaril.selftest");
  assert.deepEqual(sel.items, ["silmaril.selftest.open", "silmaril.selftest.languages"]);
  assert.deepEqual(S.namespaceItems(S.namespaceNode(t, "silmaril")).sort(),
    ["silmaril.all", "silmaril.selftest.languages", "silmaril.selftest.languages.json_has_one", "silmaril.selftest.open"]);
  assert.equal(S.namespaceNode(t, "nope"), null);
});

test("a database row's established codes may be a group_concat string", () => {
  assert.equal(co({ summary: "UNS", arity: 0, expect: "CSA", established: "UNS CSA" }), "CTH/match");
  assert.equal(co({ summary: "SAT", arity: 1, established: "SAT,CSA" }), "NOC/none");
  assert.deepEqual(st({ summary: "OPN", arity: 0, expected_open: "consistency" }).attention, { list: null, excluded: "expected-open" });
});
