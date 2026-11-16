// The logic graph pages (docs/projects/logic-graph.md), in Chromium, on a site built from silmaril's own project
// (`make pages`):
// * Logic graph is in the navigation; the graph draws the registered institutions with typed, directed edges,
//   its legend names every edge kind and direction, and the level, edge-kind, search and go-to controls work and
//   are kept in the URL; a deep link selects and details one node or edge; Fit, zoom and Reset work;
// * the table lists every node and edge and filters and sorts; the five registries list their records, filter,
//   and link to detail pages with source declarations, endpoints, facts and crosslinks;
// * the coverage page shows the audit (with omitted declarations), the pinned Hets list and the pending families;
// * a narrow (phone) viewport stacks the graph and its details; no page error anywhere.
//   node logic.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8803;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "logic_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const open = async (hash) => { await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`); await settle(); await p.waitForTimeout(300); };
  const shot = async (name, full = true) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: full }); } };
  const rows = (sel) => p.evaluate((sel) => [...document.querySelectorAll(sel + " tbody tr")].filter((tr) => !tr.hidden).map((tr) =>
    [...tr.children].map((td) => td.textContent.trim())), sel);
  const counts = () => p.evaluate(() => Object.fromEntries([...document.querySelectorAll(".lg-tabs a")].map((a) => [a.getAttribute("href").slice(2), +(a.querySelector("span") || { textContent: "-1" }).textContent])));

  // the graph
  await open("/logic-graph/");
  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav.includes("#/logic-graph"), "Logic graph is in the navigation");
  const n = await counts();
  check(n.institutions > 10 && n.comorphisms > 5 && n.morphisms >= 1 && n.rooms >= 1 && n.corridors >= 1, `registry counts ${JSON.stringify(n)}`);
  const g0 = await p.evaluate(() => window.explore.logicGraph);
  check(g0 && g0.level === "institution" && g0.nodes === n.institutions && g0.edges === n.comorphisms + n.morphisms, `the institution level draws every institution and institution edge ${JSON.stringify(g0)}`);
  const legend = await p.evaluate(() => document.getElementById("lg-legend").textContent);
  check(/comorphism.*sentences →, models ←/.test(legend) && /morphism.*sentences ←, models →/.test(legend) && /corridor/.test(legend), "the legend names each edge kind and its direction");
  await shot("logic-graph");
  // filters: morphisms only
  await p.uncheck("input.lg-kind[value=comorphism]");
  await p.waitForTimeout(400);
  const g1 = await p.evaluate(() => window.explore.logicGraph);
  check(g1.edges === n.morphisms, `edge-kind filter: morphisms only (${g1.edges})`);
  check(/kinds=morphism%2Ccorridor|kinds=morphism,corridor/.test(await p.evaluate(() => location.hash)), "the filter is kept in the URL");
  await p.uncheck("#lg-iso"); await p.waitForTimeout(400);
  const g2 = await p.evaluate(() => window.explore.logicGraph);
  check(g2.nodes < g1.nodes && g2.nodes >= 2, `hiding unconnected nodes (${g1.nodes} → ${g2.nodes})`);
  await p.click("#lg-reset"); await settle(); await p.waitForTimeout(400);
  check((await p.evaluate(() => window.explore.logicGraph)).edges === g0.edges, "Reset restores every edge");
  // levels
  await p.selectOption("#lg-level", "both"); await p.waitForTimeout(500);
  const g3 = await p.evaluate(() => window.explore.logicGraph);
  check(g3.nodes === n.institutions + n.rooms && g3.fibers >= 1, `both levels: rooms with their fibers ${JSON.stringify(g3)}`);
  await shot("logic-graph-both");
  // search
  await p.fill("#lg-q", "first-order"); await p.waitForTimeout(600);
  check(/match/.test(await p.textContent("#lg-count")), "search highlights matches");
  // a deep link selects an edge and details it
  const edge = await p.evaluate(() => [...document.querySelectorAll("#lg-go option")].map((o) => o.value).find((v) => v.startsWith("comorphism:")));
  await open("/logic-graph/" + encodeURIComponent(edge));
  const side = await p.textContent("#lgside");
  check(/comorphism/.test(side) && /from/.test(side) && /to/.test(side) && /declaration/.test(side), `deep link ${edge} details the edge`);
  check(await p.evaluate((id) => window.explore && document.querySelector("#lg-go").value === id, edge), "go-to shows the selection");
  await shot("logic-graph-selected");
  // go to a room switches the level
  const room = await p.evaluate(() => [...document.querySelectorAll("#lg-go option")].map((o) => o.value).find((v) => v.startsWith("room:")));
  await p.selectOption("#lg-go", room); await p.waitForTimeout(600);
  check((await p.evaluate(() => window.explore.logicGraph)).level !== "institution" && /room/.test(await p.textContent("#lgside")), "go to a room switches to the room level");
  // zoom and fit keep a graph drawn
  await p.click("#lg-zin"); await p.click("#lg-fit");
  check(await p.evaluate(() => !!document.querySelector("#lgcy canvas")), "zoom and fit keep the canvas");

  // the table
  await open("/logic-table/");
  const all = await rows("#lg-all");
  check(all.length === n.institutions + n.rooms + n.comorphisms + n.morphisms + n.corridors, `the table lists every node and edge (${all.length})`);
  await p.fill("#lg-all-q", "morphism"); await p.waitForTimeout(200);
  const fm = await rows("#lg-all");
  check(fm.length > 0 && fm.length < all.length && /of/.test(await p.textContent("#lg-all-n")), `filter (${fm.length})`);
  check(/q=morphism/.test(await p.evaluate(() => location.hash)), "the table filter is kept in the URL");
  await p.fill("#lg-all-q", ""); await p.click("#lg-all th[data-j='1'] button");
  check(await p.getAttribute("#lg-all th[data-j='1']", "aria-sort") === "ascending", "sorting by a column");
  await shot("logic-table");

  // the registries and a detail page each
  for (const [route, kind] of [["institutions", "institution"], ["comorphisms", "comorphism"], ["morphisms", "morphism"], ["rooms", "room"], ["corridors", "corridor"]]) {
    await open("/" + route);
    const rs = await rows(`#lg-${route}`);
    check(rs.length === n[route], `${route}: ${rs.length} rows`);
    const href = await p.evaluate((t) => document.querySelector(`#lg-${t} tbody tr a`).getAttribute("href"), route);
    await open(href.slice(1));
    const dl = await p.textContent("main");
    check(dl.includes("Lean declaration") && dl.includes(kind) && (kind === "institution" || kind === "room" ? /outgoing/.test(dl) : /from/.test(dl) && /direction/.test(dl)),
      `${kind} page ${href} has its declaration, ${kind === "institution" || kind === "room" ? "edges" : "endpoints and direction"}`);
    if (route === "comorphisms") await shot("logic-comorphism");
  }
  await open("/institutions");
  await shot("logic-institutions");

  // coverage
  await open("/logic-coverage/");
  const cov = await p.textContent("main");
  check(/Audit of Lean declarations/.test(cov) && /declarations/.test(cov) && /omitted/.test(cov), "coverage: the audit");
  check((await rows("#lg-hets")).length === 39 + 75, "coverage: the pinned Hets list (39 logics, 75 comorphisms)");
  const catRows = await rows("#lg-catalogue");
  const catDb = await p.evaluate(() => document.querySelectorAll("#lg-catalogue tbody tr").length);
  check(catDb === 295 || catDb === 0, `coverage: the curated catalogue, entry by entry (${catDb} rows)`);
  if (catDb) {
    const statuses = new Set(catRows.map((r) => r[3]));
    check(["registered", "represented", "not-institution-typed", "prospective"].every((x) => statuses.has(x)), `catalogue statuses ${[...statuses]}`);
    check(catRows.filter((r) => r[3] === "not-institution-typed").every((r) => r[6].length > 0), "every entry that is not institution-typed says why");
    check(catRows.filter((r) => r[3] === "registered").every((r) => r[4].length > 0), "every registered entry names its records");
  }
  const exRows = await rows("#lg-exclusions");
  check(exRows.length > 0 && exRows.every((r) => r[3].length > 0), `coverage: what the graph leaves out, each with a reason (${exRows.length})`);
  check(["unregistrable-declaration", "fixture-dependent", "out-of-scope"].every((c) => exRows.some((r) => r[0] === c)), "all three exclusion categories are listed");
  check(/Logic families not yet in this repository/.test(cov) && (/pending-port|in-review/.test(cov) || /None listed/.test(cov)),
    "coverage: the pending families (or that none is listed)");
  await shot("logic-coverage");

  // a phone
  const m = await b.newPage({ viewport: { width: 390, height: 844 }, isMobile: true });
  m.on("pageerror", (e) => errors.push(e.message));
  await m.goto(`http://127.0.0.1:${port}/index.html#/logic-graph/` + encodeURIComponent(edge));
  await m.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  await m.waitForTimeout(600);
  const box = await m.evaluate(() => { const a = document.getElementById("lgcy").getBoundingClientRect(), s = document.getElementById("lgside").getBoundingClientRect();
    return { cyW: a.width, sideTop: s.top, cyBottom: a.bottom, scrollW: document.documentElement.scrollWidth }; });
  check(box.cyW <= 390 && box.sideTop >= box.cyBottom - 1, `narrow: the details stack under the graph ${JSON.stringify(box)}`);
  if (shots) await m.screenshot({ path: path.join(shots, "logic-graph-phone.png"), fullPage: true });
  await m.goto(`http://127.0.0.1:${port}/index.html#/comorphisms`);
  await m.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  if (shots) await m.screenshot({ path: path.join(shots, "logic-comorphisms-phone.png"), fullPage: false });

  check(errors.length === 0, `no page errors ${JSON.stringify(errors)}`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all passed");
