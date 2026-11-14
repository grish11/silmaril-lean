// The Wasm function page's graph variants and named dominator bases (issue #231), on synthetic
// fixtures only: no production data has variants yet, and nothing here is a semantic graph.
// Builds a copy of SITE_DIR in which rust_door's `enter` (function 5) gets two variants:
// * `fx-trap-effect`, the data's `default`: flow edges without those to trap, one basis, an
//   intended relation (a made-up name; the page must show it as unchecked metadata);
// * `fx-bad-kernel`: the explicit-sink edges minus one effect edge, naming rust_door's kernel
//   table, which must then not be shown as evidence.
// Checks the default, the selector and links, what is said about each, and that the top-level
// graph keeps its kernel-checked comparison.
//   node wasm_cfg_variants.mjs SITE_DIR [SHOTS_DIR]      (as for wasm_cfg.mjs)
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const fx = fs.mkdtempSync(path.join(os.tmpdir(), "wasm-cfg-variants-"));
for (const f of ["index.html", "project.sqlite", "explore-sw.js"]) if (fs.existsSync(path.join(site, f))) fs.copyFileSync(path.join(site, f), path.join(fx, f));
fs.mkdirSync(path.join(fx, "wasm/m"), { recursive: true });
fs.copyFileSync(path.join(site, "wasm/index.json"), path.join(fx, "wasm/index.json"));
const slug = "silmaril.wasm.examples.rust_door";
const mod = JSON.parse(fs.readFileSync(path.join(site, "wasm/m", slug + ".json")));
const cfg = mod.bodies.find((b) => b.idx === 5).cfg;
const dropped = cfg.edges.findIndex((e) => e[2] === "effect");
cfg.variants = {
  "fx-trap-effect": { model: "trap-as-effect (synthetic test fixture)", label: "fixture", entry: cfg.entry,
    edges: cfg.edges.filter((e) => e[2] === "flow" && e[1] !== "trap"), bases: [{ id: "flow", kinds: ["flow"] }],
    relation: "Fixture.NotARelation" },
  "fx-bad-kernel": { model: "explicit-sink", entry: cfg.entry, edges: cfg.edges.filter((e, i) => i !== dropped),
    bases: [{ id: "fe", kinds: ["flow", "effect"], kernelTable: "silmaril.wasm.blockcfg.rust_door.enter", default: true }] } };
cfg.default = "fx-trap-effect";
fs.writeFileSync(path.join(fx, "wasm/m", slug + ".json"), JSON.stringify(mod));
const port = 8797;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", fx, "--port", String(port), "--log", path.join(fx, "requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME || "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const open = async (h) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#/wasm-func/${slug}/5${h}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.locator("#wcfg").scrollIntoViewIfNeeded(); await p.screenshot({ path: path.join(shots, name + ".png") }); } };
  const text = (sel) => p.evaluate((s) => document.querySelector(s)?.textContent ?? null, sel);
  const domNote = async () => { await p.click("#wdom"); return p.evaluate(() => ({ t: document.querySelector("#wdomnote").textContent, lean: !!document.querySelector("#wprov .prov-lean") })); };

  await open("");
  check(await p.evaluate(() => $("#wvariant").value) === "fx-trap-effect", "the data's default variant is shown first");
  const info = await text("#wvariantinfo");
  check(/Fixture\.NotARelation/.test(info) && /not checked here/.test(info) && /No theorem shown on this page says that executions follow this graph/.test(info),
    "a variant's relation is shown as unchecked metadata");
  check(await text("#wmaynote") === null && (await p.evaluate(() => wcy.edges(".may").length)) === 0, "a variant without effect edges has no may-edges and no may-edge note");
  const want = cfg.variants["fx-trap-effect"].edges.length;
  check(await p.evaluate(() => wcy.edges().length) === want, `it draws exactly its ${want} edges`);
  let d = await domNote();
  check(d.t.startsWith("fx-trap-effect") && d.t.includes(`the ${want} edges of basis “flow edges”`) && !d.lean, "dominators name the variant and basis, with no kernel badge");
  await shot("fixture-variant-default");

  await open("/@fx-bad-kernel");
  d = await domNote();
  check(/is not shown as evidence/.test(d.t) && /its edges/.test(d.t) && !d.lean, "a kernel table whose edges differ is not shown as evidence");
  await shot("fixture-bad-kernel");

  await open("/@top");
  check(await p.evaluate(() => $("#wvariant").value) === "top" && /Syntactic block CFG/.test(await text("main")), "@top is the explicit-sink graph with its caveats");
  check((await p.evaluate(() => wcy.edges(".may").length)) === cfg.edges.filter((e) => e[2] === "effect").length, "the top-level graph keeps its may-edges");
  await p.selectOption("#wbasis", "flow+effect");
  d = await domNote();
  check(d.lean && /is the same graph \(nodes, entry, edges\) and the same tree/.test(d.t), "the top-level graph keeps its kernel-checked comparison");

  await open("/@fx-trap-effect/b1");
  check(await p.evaluate(() => wcy.nodes(".sel").map((n) => n.id()).join() === "b1" && location.hash.endsWith("/@fx-trap-effect/b1")), "direct link to a node of a variant");
  await p.selectOption("#wvariant", "top");
  await p.waitForFunction(() => location.hash.includes("/@top") && !window.explore.busy && wcy && wcy.nodes(".sel").length === 1);
  check(await p.evaluate(() => location.hash.endsWith("/@top/b1")), "switching the variant keeps the selected node in the link");

  await open("/@nope");
  check(await p.evaluate(() => $("#wvariant").value) === "fx-trap-effect", "an unknown variant falls back to the default");
  check(errors.length === 0, `no page errors ${errors.join("; ")}`);
} finally {
  await b.close(); srv.kill(); fs.rmSync(fx, { recursive: true, force: true });
}
console.log(fails.length ? `${fails.length} FAILED` : "all ok");
process.exit(fails.length ? 1 : 0);
