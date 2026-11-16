// The explorer's shared shell, in Chromium: the navigation built from the registered views, the
// compact source button and its dialog (keyboard, Escape, focus), neutral status badges, and
// switching databases while views are loading: repeated graph navigation and file switches must
// leave no error, no page error and the last chosen database open.
//
//   node shell.mjs SITE_DIR [SHOTS_DIR]   (SITE_DIR holds index.html and project.sqlite)
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8795;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "shell_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 900 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  // after an open: wait until the database count has grown and the view has settled
  const opened = async (n) => { await p.waitForFunction((n) => (window.explore.opened || 0) >= n, n, { timeout: 60000 }); await settle(); };
  const count = () => p.evaluate(() => window.explore.opened || 0);
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  const errs = () => p.evaluate(() => [...document.querySelectorAll("#main .err")].map((e) => e.textContent.slice(0, 200)));
  const shot = async (n) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, n) }); } };
  await p.goto(`http://127.0.0.1:${port}/index.html#/problems`);
  await settle();

  // navigation and the view registry
  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav[0] === "#/summary" && nav.includes("#/graph") && nav.includes("#/sql"), `navigation from the registry: ${nav.join(" ")}`);
  check(await p.evaluate(() => typeof Explorer.registerView === "function" && typeof Explorer.ui.dialog === "function" && Object.isFrozen(Explorer)),
    "Explorer API is exposed and frozen");
  check(await p.evaluate(() => { try { Explorer.registerView({ id: "summary", render: () => "" }); return false; } catch (e) { return true; } }),
    "a view id cannot be registered twice");

  // compact source button and its dialog
  const src = await p.evaluate(() => ({ text: $("#source").textContent, h: $("#source").getBoundingClientRect().height }));
  check(/^project\.sqlite\s+lazy$/.test(src.text.trim()) && src.h < 30, `compact source button: "${src.text.trim()}", ${src.h}px high`);
  await p.focus("#source");
  await p.keyboard.press("Enter");
  await p.waitForSelector("dialog.dlg[open]");
  const dlg = await p.evaluate(() => { const d = document.querySelector("dialog.dlg"); return { label: document.getElementById(d.getAttribute("aria-labelledby")).textContent,
    text: d.textContent, focusIn: d.contains(document.activeElement), file: !!d.querySelector("input[type=file]") }; });
  check(dlg.label === "Database" && /lazy \(HTTP Range/.test(dlg.text) && /silmaril\.project-db/.test(dlg.text), "the dialog names the source, the read mode and the schema");
  check(dlg.focusIn && dlg.file, "focus moves into the dialog, which has a file picker");
  await shot("source-dialog.png");
  await p.keyboard.press("Escape");
  await p.waitForFunction(() => !document.querySelector("dialog.dlg"));
  check(await p.evaluate(() => !document.querySelector("dialog.dlg") && document.activeElement === $("#source")), "Escape closes it and focus returns to the button");

  // neutral status badges, one status column
  const st = await p.evaluate(() => ({ heads: [...document.querySelectorAll("#list th")].map((t) => t.textContent),
    badges: [...document.querySelectorAll("#list .st")].map((s) => s.textContent), coloured: document.querySelectorAll("#list .badge").length,
    wrap: getComputedStyle(document.querySelector("#list td.nw")).whiteSpace }));
  check(st.heads.filter((h) => /status|verdict|summary/.test(h)).length === 1 && st.coloured === 0, `one status column, no verdict colour badges (${st.heads.join(",")})`);
  check(st.badges.length > 0 && st.badges.every((t) => /^[A-Z]{3}(·true|·false)?[!✓]?$/.test(t)) && st.wrap === "nowrap", `three-character badges: ${[...new Set(st.badges)].join(" ")}`);
  // contingent is shown as SZS NoConsequence, and the title keeps the stored code
  const noc = await p.evaluate(() => Explorer.ui.statusBadge({ summary: "contingent", verdict: "fails" }));
  check(/>NOC</.test(noc) && /stored as &quot;contingent&quot;/.test(noc) && /NoConsequence/.test(noc), "contingent shows as NOC, naming the stored code");
  check(await p.evaluate(() => ["THM", "OPN", "SAT", "UNS", "CSA", "UNK"].every((c) => Explorer.ui.statusCode(c) === c)), "SZS codes are shown as stored");
  // Expectation outcomes (the shared status API), compared as `sil project check` W1 does: met when
  // the expectation is the summary or an established status (the arity-0 closure THM ⇒ SAT,
  // UNS ⇒ CSA), or the summary is contingent and SAT or CSA is expected. No expectation is
  // neutral whatever the verdict; a known summary that does not meet it is an error; an unknown
  // one is neutral. Closed propositions show their truth value; stored codes are kept.
  const shape = await p.evaluate(() => {
    const b = (s) => { const d = document.createElement("div"); d.innerHTML = Explorer.ui.statusBadge(s); const e = d.firstChild;
      return { text: e.textContent, code: e.dataset.code, outcome: e.dataset.outcome, title: e.title }; };
    return {
      // l65: a closed membership refuted (UNS, closure CSA) with the generator's expect CSA
      l65: b({ summary: "UNS", verdict: "fails", arity: 0, expect: "CSA", established: ["UNS", "CSA"] }),
      l65NoStatuses: b({ summary: "UNS", verdict: "fails", arity: 0, expect: "CSA" }),
      closedFalseNoExpect: b({ summary: "UNS", verdict: "fails", arity: 0 }),
      closedTrue: b({ summary: "THM", verdict: "holds", arity: 0, expect: "THM", established: ["THM", "SAT"] }),
      // the closure goes one way: CSA alone does not establish UNS
      csaExpectedUns: b({ summary: "CSA", verdict: "fails", arity: 0, expect: "UNS", established: ["CSA"] }),
      closedTrueExpectedFalse: b({ summary: "THM", verdict: "holds", arity: 0, expect: "UNS", established: ["THM", "SAT"] }),
      openUnsExpectedThm: b({ summary: "UNS", verdict: "unknown", arity: 1, expect: "THM", established: ["UNS"] }),
      pending: b({ summary: "OPN", verdict: "unknown", arity: 0, expect: "THM", established: [] }),
      genuine: b({ summary: "CSA", verdict: "fails", arity: 0, finding: "error" }),
      nocNoExpect: b({ summary: "contingent", verdict: "fails", arity: 1, established: ["SAT", "CSA"] }),
      nocExpectSat: b({ summary: "contingent", verdict: "fails", arity: 1, expect: "sat", established: ["SAT", "CSA"] }),
      // an empty carrier: THM and UNS both hold vacuously; that alone is no error
      emptyBoth: b({ summary: "THM", verdict: "holds", arity: 1, established: ["THM", "UNS"] }),
      emptyExpectUns: b({ summary: "THM", verdict: "holds", arity: 1, expect: "UNS", established: ["THM", "UNS"] }),
    };
  });
  const o = (k) => `${shape[k].text}/${shape[k].outcome}`;
  check(o("l65") === "UNS·false✓/match" && o("l65NoStatuses") === "UNS·false✓/match",
    `a refuted closed example expected CSA meets it through the closure (${o("l65")}, ${o("l65NoStatuses")})`);
  check(o("closedFalseNoExpect") === "UNS·false/none" && o("closedTrue") === "THM·true✓/match", `closed propositions show their truth value (${o("closedFalseNoExpect")}, ${o("closedTrue")})`);
  check(o("csaExpectedUns") === "CSA·false!/mismatch", `CSA does not establish UNS (${o("csaExpectedUns")})`);
  check(o("closedTrueExpectedFalse") === "THM·true!/mismatch" && o("openUnsExpectedThm") === "UNS!/mismatch" && /UNEXPECTED: expected THM/.test(shape.openUnsExpectedThm.title),
    "a known status that does not meet the expectation is an error");
  check(o("pending") === "OPN/pending" && /expected THM, not established yet/.test(shape.pending.title), "an unknown status is neutral, naming the expectation");
  check(o("genuine") === "CSA·false!/error", "a genuine-error finding is an error");
  check(o("nocNoExpect") === "NOC/none" && shape.nocNoExpect.code === "contingent" && o("nocExpectSat") === "NOC✓/match",
    `contingent: neutral without an expectation, meets an expected SAT (${o("nocNoExpect")}, ${o("nocExpectSat")})`);
  check(o("emptyBoth") === "THM/none" && o("emptyExpectUns") === "THM✓/match", "vacuous THM and UNS over an empty carrier are no error");
  const agg = await p.evaluate(() => [
    Explorer.ui.expectationSummary([{ summary: "THM", verdict: "holds", arity: 0, expect: "THM" }, { summary: "UNS", verdict: "fails", arity: 0, expect: "CSA" }]),
    Explorer.ui.expectationSummary([{ summary: "THM", verdict: "holds", arity: 0, expect: "THM" }, { summary: "OPN", verdict: "unknown", arity: 0, expect: "THM" }]),
    Explorer.ui.expectationSummary([{ summary: "THM", verdict: "holds", arity: 0, expect: "THM" }, { summary: "THM", verdict: "holds", arity: 0 }])]);
  check(agg[0].allMet && !agg[1].allMet && agg[1].pending === 1 && !agg[2].allMet && agg[2].unset === 1,
    "all expectations met only when every problem has one and meets it (unknown and missing are not a pass)");
  const listed = await p.evaluate(() => [...document.querySelectorAll("#list .st[data-code=contingent]")].map((e) => e.textContent));
  check(listed.every((t) => /^NOC[!✓]?$/.test(t)), `contingent rows of the database display as NOC (${listed.length} on this page)`);
  await shot("problems.png");

  // sections: another task adds a block to artifact pages without editing the view; a section
  // that throws shows its error and the page still renders
  await p.evaluate(() => {
    Explorer.registerSection({ id: "test-ok", title: "Test section", on: ["artifact", "wasm-module"],
      render: (s) => s.cid ? `<p id="sec-ok">${Explorer.ui.esc(s.kind + " " + s.cid)} <a href="#/languages/x">language</a></p>` : "" });
    Explorer.registerSection({ id: "test-throws", title: "Broken section", on: ["artifact"], render: () => { throw new Error("boom"); } });
  });
  await p.evaluate(() => { location.hash = "#/artifacts"; });
  await settle();
  const first = await p.evaluate(() => document.querySelector("#list td a").getAttribute("href"));
  await p.evaluate((h) => { location.hash = h; }, first);
  await settle();
  const sec = await p.evaluate(() => ({ ok: (document.querySelector("#sec-ok") || {}).textContent || "",
    err: (document.querySelector("section[data-section=test-throws] .err") || {}).textContent || "", facts: /Facts/.test(document.querySelector("#main").innerText) }));
  check(/^artifact bafkr/.test(sec.ok) && sec.err === "boom" && sec.facts, `sections render on artifact pages (${sec.ok.slice(0, 30)}…), a failing one is contained`);
  check(await p.evaluate(() => { try { Explorer.registerSection({ id: "x", on: ["nowhere"], render: () => "" }); return false; } catch (e) { return true; } }), "a section names known subjects");
  await p.evaluate(() => { location.hash = "#/problems"; });
  await settle();

  // repeated graph navigation: every hash change starts a new route while the last one may still run
  const names = await p.evaluate(() => [...document.querySelectorAll("#list td a")].map((a) => a.textContent).slice(0, 12));
  for (let i = 0; i < names.length; i++) {
    await p.evaluate((h) => { location.hash = h; }, "#/graph/" + encodeURIComponent(names[i]));
    if (i % 3 === 2) await settle(); else await p.waitForTimeout(30);
  }
  await settle();
  const g = await p.evaluate(() => ({ view: window.explore.view, nodes: cy ? cy.nodes().length : 0, focus: $("#gfocus") && $("#gfocus").value }));
  check(g.view === "graph" && g.nodes > 0 && g.focus === names[names.length - 1], `the last graph wins: ${g.nodes} nodes, focus ${g.focus}`);
  check((await errs()).length === 0, "no error after rapid graph navigation");

  // switching databases while a view loads: a local copy, then the default URL, then the copy again
  const bytes = fs.readFileSync(path.join(site, "project.sqlite"));
  const tmp = path.join(os.tmpdir(), "shell-copy.sqlite");
  fs.writeFileSync(tmp, bytes);
  for (let i = 0; i < 3; i++) {
    await p.evaluate(() => { location.hash = "#/graph"; });
    let n = await count();
    await p.click("#source");
    await p.setInputFiles("dialog.dlg input[type=file]", tmp);
    await p.evaluate(() => { location.hash = "#/problems"; });
    await opened(n + 1);
    check(window_ok(await p.evaluate(() => ({ src: window.explore.source, mode: window.explore.mode }))), `switch ${i + 1}: the chosen file is open`);
    n = await count();
    await p.click("#source");
    await p.fill("dialog.dlg input[name=u]", "project.sqlite");
    await p.click("dialog.dlg form button");
    await p.evaluate(() => { location.hash = "#/graph"; });
    await opened(n + 1);
    check(await p.evaluate(() => window.explore.source === "project.sqlite" && /^lazy/.test(window.explore.mode)), `switch ${i + 1}: back to the lazy URL`);
    check((await errs()).length === 0, `switch ${i + 1}: no error`);
  }
  await shot("graph-after-switches.png");
  check(errors.length === 0, "no page errors " + errors.join("; "));
} finally {
  await b.close(); srv.kill();
}
function window_ok(s) { return s.src === "shell-copy.sqlite" && s.mode === "local file"; }
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all ok");
