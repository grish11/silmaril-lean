// Unit tests of the component-tests view (src/project/explore/views/component-tests.js) on the
// committed data (examples/component-tests): every binary, its rows, expectations, theorem
// strength and the oracle's verdict are shown, and the report, the oracle and the files agree on
// the bytes.
//
//   node --test tools/silmaril-project/tests/explore/component_tests_view.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import { createRequire } from "node:module";
import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.join(here, "../../../..");
const dir = path.join(root, "examples/component-tests");
const CT = createRequire(import.meta.url)(path.join(here, "../../src/project/explore/views/component-tests.js"));
const report = JSON.parse(fs.readFileSync(path.join(dir, "report.json"), "utf8"));
const oracle = JSON.parse(fs.readFileSync(path.join(dir, "oracle.json"), "utf8"));
const sha = (f) => createHash("sha256").update(fs.readFileSync(path.join(dir, f))).digest("hex");

test("the report, the oracle and the committed binaries name the same bytes", () => {
  assert.deepEqual(report.binaries.map((b) => b.name).sort(), Object.keys(oracle.binaries).sort());
  for (const b of report.binaries) {
    assert.equal(b.sha256, sha(b.wasm), b.wasm);
    assert.equal(b.size, fs.statSync(path.join(dir, b.wasm)).size, b.wasm);
    assert.equal(oracle.binaries[b.name].sha256, b.sha256, b.name);
    assert.ok(fs.existsSync(path.join(dir, b.wat)), b.wat);
  }
});

test("the decoder bridge regressions name their bytes; only a proved disproof claims one", () => {
  const regs = report.regressions || [];
  assert.deepEqual(regs.map((g) => g.name), ["instexport", "paramname"]);
  // instexport demonstrates a mismatch only; paramname carries the proved `not_startAdequacy`.
  assert.equal(regs.find((g) => g.name === "instexport").disproof, undefined);
  assert.equal(regs.find((g) => g.name === "paramname").disproof,
    "Silmaril.Wasm.Component.DecoderBridge.not_startAdequacy");
  const h = CT.render(report, oracle, {});
  for (const g of regs) {
    assert.equal(g.sha256, sha(g.wasm), g.wasm);
    assert.equal(g.size, fs.statSync(path.join(dir, g.wasm)).size, g.wasm);
    assert.ok(fs.existsSync(path.join(dir, g.wat)), g.wat);
    assert.ok(!(g.name in oracle.binaries), g.name);
    assert.ok(h.includes(g.wasm) && h.includes(g.sha256), g.name);
    for (const f of g.facts) assert.ok(h.includes(f.theorem), f.theorem);
    if (g.disproof) {
      // A claimed disproof names a theorem listed among the facts, shown on the page.
      assert.ok(g.facts.some((f) => f.theorem === g.disproof), g.name);
      assert.ok(h.includes(g.disproof), g.name);
      assert.ok(g.status.includes("counterexample proved"), g.name);
    } else {
      assert.ok(g.status.includes("not a disproof"), g.name);
    }
  }
  assert.ok(h.includes("Decoder bridge regressions"));
});

test("the oracle agrees with the expectations", () => {
  const s = oracle.binaries.starts, t = oracle.binaries.trap;
  assert.deepEqual(s.observed, { instantiates: true, import_trace: [1, 2], calls: 2, get: 42 });
  assert.deepEqual(t.observed, { instantiates: false, trap: true });
  assert.ok(s.agrees && t.agrees);
  assert.equal(oracle.tools.wasmtime.version, "50.0.0");
});

test("the page shows binaries, imports, expectations, rows, strength, assumptions and the oracle", () => {
  const seen = [];
  const h = CT.render(report, oracle, { badge: (n) => { seen.push(n); return `<b data-row="${n}"></b>`; } });
  for (const b of report.binaries) {
    assert.match(h, new RegExp(`href="component-tests/${b.wasm}" download`));
    assert.ok(h.includes(b.sha256));
    for (const r of b.rows) {
      assert.ok(h.includes(`href="#/problem/${encodeURIComponent(r.name)}"`), r.name);
      assert.ok(seen.includes(r.name), r.name);
    }
    assert.ok(h.includes(b.ref.theorem));
    assert.ok(b.ref.strength.includes("Conformance.decodeRef reads from these bytes"), b.name);
    assert.ok(b.ref.strength.includes("not a general binary-to-REF equivalence"), b.name);
    assert.ok(h.includes(b.bridge.theorem), b.name);
    assert.ok(b.bridge.strength.startsWith("structural, proved for every binary (DecoderBridge.rel_of_decode)"), b.name);
    assert.ok(b.bridge.strength.includes("agree on core instantiations"), b.name);
    assert.ok(h.includes(b.bridge_wiring.theorem), b.name);
    assert.ok(b.bridge_wiring.strength.includes("in the decidable fragment DecoderBridge.InFrag (DecoderBridge.relW_of_decode)"), b.name);
    assert.ok(b.bridge_wiring.strength.includes("Syntax only"), b.name);
    assert.ok(b.bridge_semantic.startsWith("open: "), b.name);
    assert.ok(b.bridge_semantic.includes("is the open goal DecoderBridge.Task."), b.name);
  }
  const trap = report.binaries.find((b) => b.bridge_semantic.includes("Task.failAdequacy"));
  assert.ok(trap.bridge_semantic.includes("DecoderBridge.trap_of_firstCore"));
  assert.ok(trap.bridge_semantic.includes("Task.failRefWiredRest' are open"));
  const starts = report.binaries.find((b) => b.bridge_semantic.includes("Task.startAdequacy"));
  assert.ok(starts.bridge_semantic.includes("DecoderBridge.firstImp_ready_ref"));
  assert.ok(starts.bridge_semantic.includes("DecoderBridge.starts_firstImpFrag"));
  assert.ok(starts.bridge_semantic.includes("DecoderBridge.starts_of_d"));
  assert.ok(starts.bridge_semantic.includes("DecoderBridge.nodesRef"));
  assert.ok(!starts.bridge_semantic.includes("Task.laterNodesRef"));
  assert.ok(!h.includes("hand transcription"));
  assert.ok(h.includes("f: func(x: u32)"));
  assert.ok(h.includes("<code>f(1) -&gt; ()</code>, <code>f(2) -&gt; ()</code>"));
  assert.ok(h.includes("instantiation: <b>fail ()</b>"));
  assert.ok(h.includes("divergence is not observed"));
  assert.equal((h.match(/>agrees</g) || []).length, 2);
  assert.ok(h.includes("wasmtime 50.0.0"));
});

test("a differing oracle and other bytes are flagged", () => {
  const bad = JSON.parse(JSON.stringify(oracle));
  bad.binaries.starts.agrees = false;
  bad.binaries.trap.sha256 = "00";
  const h = CT.render(report, bad);
  assert.ok(h.includes("DIFFERS"));
  assert.ok(h.includes("the oracle ran on other bytes"));
});

test("without an oracle the page still renders", () => {
  const h = CT.render(report, null);
  assert.equal((h.match(/not run/g) || []).length, report.binaries.length);
});
