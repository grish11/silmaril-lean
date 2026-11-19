// Unit tests of the progress page's tallies (src/project/explore/views/progress.js): families are
// what the children edges reach, each problem counted once per family in exactly one of holds,
// fails and open; dimensions come only from `….dimension.<d>` groups.
//
//   node --test tools/silmaril-project/tests/explore/progress.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const P = createRequire(import.meta.url)(path.join(here, "../../src/project/explore/views/progress.js"));

const edges = [["root", "a"], ["root", "b"], ["a", "p1"], ["a", "p2"], ["a", "sub"], ["sub", "p3"], ["sub", "p1"],
  ["b", "p3"], ["b", "p4"], ["x.dimension.inventory", "p1"], ["x.dimension.semantic", "p2"], ["x.dimension.semantic", "g"],
  ["g", "p3"], ["g", "p1"], ["x.dimension.bogus", "p4"]];
const kids = new Map();
for (const [p, c] of edges) { if (!kids.has(p)) kids.set(p, []); kids.get(p).push(c); }
const groups = new Set(["root", "a", "b", "sub", "g", "x.dimension.inventory", "x.dimension.semantic", "x.dimension.bogus"]);
const isGroup = (n) => groups.has(n);

test("a family's problems are what its children edges reach, groups excluded, each once", () => {
  assert.deepEqual([...P.progressLeaves("a", kids, isGroup)].sort(), ["p1", "p2", "p3"]);
  assert.deepEqual([...P.progressLeaves("root", kids, isGroup)].sort(), ["p1", "p2", "p3", "p4"]);
});

test("holds + fails + open = problems; markings are counted apart", () => {
  const info = { p1: { verdict: "holds", tier: "kernel" }, p2: { verdict: "fails", tier: "compiled", finding: "error" },
    p3: { verdict: "unknown", deprecated: "self" }, p4: { verdict: "holds", axiomatic: true, detached: true } };
  const t = P.progressTally(["p1", "p2", "p3", "p4"], (n) => info[n]);
  assert.equal(t.problems, 4);
  assert.equal(t.holds + t.fails + t.open, t.problems);
  assert.deepEqual([t.holds, t.fails, t.open, t.deprecated, t.findings, t.axiomatic, t.notKernel, t.detached], [2, 1, 1, 1, 1, 1, 1, 1]);
  assert.equal(P.progressTally(["zz"], () => undefined).open, 1, "a problem with no summary is open");
});

test("dimensions come only from known dimension groups, through nested groups", () => {
  const d = P.progressDimensions([...groups], kids, isGroup);
  assert.deepEqual([...d.get("p1")].sort(), ["inventory", "semantic"]);
  assert.deepEqual([...d.get("p2")], ["semantic"]);
  assert.deepEqual([...d.get("p3")], ["semantic"]);
  assert.equal(d.has("p4"), false, "an unknown dimension name is ignored");
});
