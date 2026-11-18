// Runs lrat.wasm on Node's WebAssembly engine with the sessions of
// Silmaril/Proofs/Wasm/Examples/LRAT/Tests.lean (a test of the bytes on an independent engine,
// not a proof): one fresh instance per session, calls in order, the store persisting.
// Usage: node examples/wasm-checkers/test-lrat.mjs
import { readFileSync } from "node:fs";

const bytes = readFileSync(new URL("./lrat.wasm", import.meta.url));
const module = new WebAssembly.Module(bytes);

function check(cnf, proof) {
  const e = new WebAssembly.Instance(module, {}).exports;
  for (const clause of cnf) { for (const l of clause) e.add_lit(l); e.end_clause(); }
  for (const s of proof) {
    if (s[0] === "add") { const [, id, lits, hints] = s;
      e.step_begin(id); lits.forEach(l => e.step_lit(l)); hints.forEach(h => e.step_hint(h)); e.step_end(); }
    else if (s[0] === "del") s[1].forEach(id => e.delete(id));
    else { const [, id, lits, groups] = s;
      e.step_begin(id); lits.forEach(l => e.step_lit(l));
      for (const [j, hs] of groups) { e.rat_begin(j); hs.forEach(h => e.step_hint(h)); }
      e.rat_end(); }
  }
  return e.unsat() === 1;
}

const unitPair = [[1], [-1]];
const satTwo = [[1, 2], [-1, 2]];
const four = [[1, 2], [-1, 2], [1, -2], [-1, -2]];
const php32 = [[1, 2], [3, 4], [5, 6], [-1, -3], [-1, -5], [-3, -5], [-2, -4], [-2, -6], [-4, -6]];
const cases = [
  ["unitPair", true, unitPair, [["add", 3, [], [1, 2]]]],
  ["fourClauses", true, four, [["add", 5, [2], [1, 2]], ["add", 6, [], [5, 3, 4]]]],
  ["php32", true, php32, [["add", 10, [-1], [4, 5, 2, 3, 9]], ["add", 11, [-2], [7, 8, 2, 3, 6]],
    ["del", [4, 5, 6, 7, 8, 9]], ["add", 12, [], [10, 11, 1]]]],
  ["fourClauses RAT", true, four, [["rat", 5, [3], []], ["rat", 6, [-3, 1], [[5, [1, 3]]]],
    ["add", 7, [1], [5, 6]], ["add", 8, [], [7, 2, 4]]]],
  ["fourClauses, no proof", false, four, []],
  ["satTwo bogus RUP", false, satTwo, [["add", 3, [], [1, 2]]]],
  ["satTwo bogus RUP 2", false, satTwo, [["add", 3, [2], [1]]]],
  ["satTwo unknown hint", false, satTwo, [["add", 3, [], [7]]]],
  ["satTwo bogus RAT", false, satTwo, [["rat", 3, [-2], []], ["add", 4, [], [1, 2, 3]]]],
  ["satTwo uncovered RAT candidate", false, satTwo,
    [["rat", 3, [-2], [[1, [2]], [2, [1]]]], ["add", 4, [], [1, 2, 3]]]],
];
let failed = 0;
for (const [name, want, cnf, proof] of cases) {
  const got = check(cnf, proof);
  console.log(`${got === want ? "ok  " : "FAIL"} ${name}: unsat = ${got ? 1 : 0}`);
  if (got !== want) failed++;
}
process.exit(failed ? 1 : 0);
