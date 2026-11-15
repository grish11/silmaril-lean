// The explorer's Wasm function pages (`wasmFuncPage` in explore.html): how the block CFG draws
// its conservative may-edges, on a small function (rust_door enter) and a large one (the WASI
// adapter's poll_oneoff, 112 blocks). Checks, in a browser:
// * the legend's counts are the counts of the page data (wasm/m/<slug>.json);
// * may-edges are kept as graph elements but not drawn by default; selecting, hovering or the
//   "draw all" toggle draws them, and never moves a node (no re-layout);
// * a special node's inspector lists every edge into it; a block's lists its exact edges;
// * keyboard navigation, direct links (#/wasm-func/<slug>/<idx>/<node>) and the dominator basis;
// * the module call graph and a machine page still draw.
//   node wasm_cfg.mjs SITE_DIR [SHOTS_DIR]
// SITE_DIR holds the explorer page as index.html, its project.sqlite and the wasm/ directory
// written by wasm-pages (`make pages` writes all three to _site).
import { spawn } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8794;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", "/tmp/wasm_cfg_requests.jsonl"], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME || "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1500, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const open = async (hash) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png") }); } };
  const positions = () => p.evaluate(() => JSON.stringify(wcy.nodes().map((n) => [n.id(), Math.round(n.position("x")), Math.round(n.position("y"))])));
  // Drawn = displayed (computed style); Collection.visible() caches across class-only changes.
  const drawn = () => p.evaluate(() => { const on = (e) => e.style("display") === "element";
    return { may: wcy.edges(".may").filter(on).length, flow: wcy.edges().not(".may").filter(on).length, allMay: wcy.edges(".may").length }; });
  const legend = () => p.evaluate(() => Object.fromEntries([...document.querySelectorAll("#wlegend [data-c]")].map((x) => [x.dataset.c, Number(x.textContent)])));
  const expect = (slug, idx) => {
    const cfg = JSON.parse(fs.readFileSync(path.join(site, "wasm/m", slug + ".json"))).bodies.find((x) => x.idx === idx).cfg;
    const n = (f) => cfg.edges.filter(f).length;
    return { flow: n((e) => e[2] !== "effect"), may: n((e) => e[2] === "effect"), mayTrap: n((e) => e[2] === "effect" && e[1] === "trap"),
      mayRaise: n((e) => e[2] === "effect" && e[1] === "raise"), marked: cfg.blocks.filter((x) => x.effects.length).length,
      mayFrom: new Set(cfg.edges.filter((e) => e[2] === "effect").map((e) => e[0])).size, cfg };
  };

  for (const [slug, idx, name] of [["silmaril.wasm.examples.rust_door", 5, "door"], ["silmaril.wasm_components.adapter.reactor.blob", 127, "large"]]) {
    const t0 = Date.now();
    // The explicit-sink graph (@top), whatever the data's default view is.
    await open(`/wasm-func/${slug}/${idx}/@top`);
    const ms = Date.now() - t0;
    const want = expect(slug, idx), got = await legend();
    check(["flow", "may", "mayTrap", "mayRaise", "marked", "mayFrom"].every((k) => got[k] === want[k]), `${name}: legend counts ${JSON.stringify(got)}`);
    let d = await drawn();
    check(d.allMay === want.may && d.may === 0 && d.flow === want.flow, `${name}: all ${want.may} may-edges kept, none drawn; ${want.flow} flow edges drawn`);
    await shot(`${name}-default`);
    const before = await positions();
    await p.check("#weff");
    d = await drawn();
    check(d.may === want.may, `${name}: "draw all may-edges" draws ${d.may}/${want.may}`);
    check(await positions() === before, `${name}: drawing may-edges moves no node`);
    await shot(`${name}-all-may`);
    await p.uncheck("#weff");
    // Hover a marked block: its may-edges are drawn, and only those.
    const marked = want.cfg.blocks.findIndex((x) => x.effects.length && want.cfg.edges.some((e) => e[0] === want.cfg.blocks.indexOf(x) && e[2] === "effect"));
    const own = want.cfg.edges.filter((e) => e[0] === marked && e[2] === "effect").length;
    await p.evaluate((id) => wcy.getElementById(id).emit("mouseover"), "b" + marked);
    check((await drawn()).may === own, `${name}: hovering b${marked} draws its ${own} may-edge(s)`);
    await p.evaluate((id) => wcy.getElementById(id).emit("mouseout"), "b" + marked);
    check((await drawn()).may === 0, `${name}: leaving it hides them again`);
    check(await positions() === before, `${name}: hovering moves no node`);
    // Select trap: every edge into it is listed and drawn.
    await p.selectOption("#wgo", "trap");
    const intoTrap = want.cfg.edges.filter((e) => e[1] === "trap");
    const listed = await p.evaluate(() => document.querySelectorAll("#wside .wedges button.wnode").length);
    check(listed === intoTrap.length, `${name}: trap's inspector lists ${listed}/${intoTrap.length} edges in`);
    check((await drawn()).may === want.mayTrap, `${name}: selecting trap draws its ${want.mayTrap} may-edges`);
    check((await p.evaluate(() => location.hash)).endsWith(`/${idx}/@top/trap`), `${name}: the address bar links to the selected node`);
    await shot(`${name}-trap-selected`);
    // Keyboard: focus the graph, j selects b0, ArrowDown its first flow successor, Escape clears.
    await p.keyboard.press("Escape");
    await p.focus("#wcy");
    await p.keyboard.press("Escape");
    await p.keyboard.press("j");
    check(await p.evaluate(() => wcy.nodes(".sel").map((n) => n.id()).join()) === "b0", `${name}: key j selects b0`);
    const succ0 = want.cfg.edges.find((e) => e[0] === 0 && e[2] !== "effect");
    await p.keyboard.press("ArrowDown");
    const s1 = await p.evaluate(() => wcy.nodes(".sel").map((n) => n.id()).join());
    check(s1 === (typeof succ0[1] === "number" ? "b" + succ0[1] : succ0[1]), `${name}: ArrowDown follows a flow edge to ${s1}`);
    check(await p.evaluate(() => /flow successors/.test(document.querySelector("#wside").textContent)), `${name}: the inspector shows the block's edges`);
    await p.keyboard.press("Escape");
    check(await p.evaluate(() => wcy.nodes(".sel").length === 0 && /\/@top$/.test(location.hash)), `${name}: Escape clears the selection and the link`);
    // Dominator tree: the basis is explicit and switchable.
    await p.click("#wdom");
    check(await p.evaluate((n) => document.querySelector("#wdomnote").textContent.includes(`the ${n} edges of basis “flow edges”`), want.flow), `${name}: dominator basis stated (flow edges only)`);
    await p.selectOption("#wbasis", "flow+effect");
    check(await p.evaluate((n) => document.querySelector("#wdomnote").textContent.includes(`the ${n} edges of basis “flow + effect”`), want.flow + want.may), `${name}: dominator basis switched to flow + may-edges`);
    if (name === "door") check(await p.evaluate(() => /kernel-checked table of .* is the same graph \(nodes, entry, edges\) and the same tree, compared here node by node/.test(document.querySelector("#wdomnote").textContent)),
      "door: on flow + may-edges the browser tree equals the Lean kernel-checked table");
    else check(await p.evaluate(() => !/kernel-checked table/.test(document.querySelector("#wdomnote").textContent)), `${name}: no kernel table is claimed`);
    await shot(`${name}-dominators`);
    await p.selectOption("#wbasis", "flow");
    await p.click("#wflat");
    check(await positions() === before, `${name}: returning to the flat CFG keeps the layout`);
    console.log(`     ${name}: page ready in ${ms} ms`);
  }
  // The data's default graph (when it names one, e.g. all-effects): shown first, with its own
  // counts; outcomes are marks, not may-edges; no special node it does not have.
  for (const [slug, idx] of [["silmaril.wasm.examples.rust_door", 5], ["silmaril.wasm_components.adapter.reactor.blob", 127]]) {
    const top = expect(slug, idx).cfg;
    if (!top.default || !top.variants || !top.variants[top.default]) { console.log(`     ${slug}/${idx}: the data names no default variant`); continue; }
    const v = top.variants[top.default];
    // A contracted graph (members) must be the quotient of the all-effects graph: every AE edge but
    // the merged fall-throughs (consecutive members), mapped to groups; every outcome kept per member.
    const ae = top.variants["all-effects"];
    if (Array.isArray(v.members) && ae) {
      const grp = new Map(); v.members.forEach((ms, gi) => ms.forEach((k) => grp.set(k, gi)));
      const inner = new Set(v.members.flatMap((ms) => ms.slice(1).map((k, j) => ms[j] + ">" + k)));
      const G = (x) => typeof x === "number" ? grp.get(x) : x;
      const want = new Set(ae.edges.filter(([a, x, k]) => !(k === "flow" && typeof x === "number" && inner.has(a + ">" + x))).map(([a, x, k]) => `${G(a)}|${G(x)}|${k}`));
      const got = new Set(v.edges.map(([a, x, k]) => `${a}|${x}|${k}`));
      check(want.size === got.size && [...want].every((x) => got.has(x)), `${slug}/${idx}: ${top.default} edges are the quotient of all-effects (${got.size} edges)`);
      check((v.outcomes || []).length === (ae.outcomes || []).length, `${slug}/${idx}: every all-effects outcome is kept, per member`);
    }
    await open(`/wasm-func/${slug}/${idx}`);
    const g = await p.evaluate(() => ({ variant: $("#wvariant").value, nodes: wcy.nodes('[kind = "block"]').length, edges: wcy.edges().not(".may").length,
      outcomes: Number(document.querySelector('[data-c="outcomes"]')?.textContent ?? 0), may: wcy.edges(".may").not(".outc").length }));
    const nn = v.granularity === "instr" ? v.nodes.length : (v.blocks || top.blocks).length;
    check(g.variant === top.default && g.nodes === nn && g.edges === v.edges.length && g.outcomes === (v.outcomes || []).length && g.may === 0,
      `${slug}/${idx}: default graph ${top.default} drawn as given (${g.nodes} nodes, ${g.edges} edges, ${g.outcomes} outcomes)`);
    await p.click("#wdom");
    const unreached = await p.evaluate(() => (/Not reached on this basis: ([^.]*)/.exec(document.querySelector("#wdomnote").textContent) || [, ""])[1]);
    check(!/\b(trap|raise)\b/.test(unreached) || v.edges.some((e) => e[1] === "trap" || e[1] === "raise"), `${slug}/${idx}: no absent sink is listed as unreached`);
    await shot(`default-${idx}`);
  }
  // Direct link to a block of the large graph: selected, inspected, in view.
  await open("/wasm-func/silmaril.wasm_components.adapter.reactor.blob/127/@top/b7");
  check(await p.evaluate(() => wcy.nodes(".sel").map((n) => n.id()).join() === "b7" && /\bb7\b/.test(document.querySelector("#wside").textContent)),
    "direct link #/…/127/b7 selects and inspects b7");
  check(await p.evaluate(() => { const bb = wcy.getElementById("b7").renderedBoundingBox(); return bb.x1 >= 0 && bb.y1 >= 0 && bb.x2 <= wcy.width() && bb.y2 <= wcy.height(); }),
    "the linked block is in view");
  await shot("large-linked-b7");
  // Hover latency on the large graph (class changes only).
  const hoverMs = await p.evaluate(() => { const t = performance.now(); for (let i = 0; i < 50; i++) { const n = wcy.getElementById("b" + i); n.emit("mouseover"); n.emit("mouseout"); } return (performance.now() - t) / 100; });
  check(hoverMs < 20, `large: a hover costs ${hoverMs.toFixed(2)} ms`);
  // No regressions elsewhere: the module call graph and a machine page draw.
  await open("/wasm-module/silmaril.wasm.examples.rust_door");
  check(await p.evaluate(() => !!wcy && wcy.nodes().length > 0), "module call graph draws");
  await open("/machine/silmaril.wasm.blockcfg.rust_door.enter");
  check(await p.evaluate(() => !!mcy && mcy.nodes().length > 0), "machine page draws");
  check(errors.length === 0, `no page errors ${errors.join("; ")}`);
} finally {
  await b.close(); srv.kill();
}
console.log(fails.length ? `${fails.length} FAILED` : "all ok");
process.exit(fails.length ? 1 : 0);
