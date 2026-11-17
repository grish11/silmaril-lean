// The acceptor-evidence section (explore/views/acceptors.js) in Chromium, on a `make pages` output
// and on fixtures built from it:
// * the site's acceptor-runs.json is the committed harness report, byte for byte
//   (tools/wasm-acceptor-harness/report.json, copied by `make pages`), and the SAT component's
//   page lists every case the report runs on its SHA-256;
// * fixture report (a match, a mismatch, a case without expectation, a case of other bytes): the
//   component and artifact pages show "Runtime observations (Wasmtime 50.0.0) — tested, not
//   proved", the exact CID and SHA-256, one row per case of these bytes only, the verdicts as
//   "matches expectation (test)" / "mismatch" / "no expectation", and no proof (green) style on
//   any observation; the Lean theorems are shown apart, with their kind of claim;
// * no report: a neutral notice and no error, the theorems still shown;
// * a malformed report: an error in the section's own block, the rest of the page rendered;
// * the static theorem map: every claim's SHA-256 is its artifact's registered one (when it is
//   registered; SAT must be), and every named theorem whose header is on this branch is stated in it.
//   node acceptor_runs.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const here = path.dirname(new URL(import.meta.url).pathname);
const repo = path.join(here, "../../../..");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const SAT = "silmaril.wasm.examples.sat_accept.component";

// The registry: name -> { cid, sha256 } (its machine-written layout, one key per line).
const registry = {};
{ let cur = null;
  for (const line of fs.readFileSync(path.join(repo, "silmaril/artifacts.toml"), "utf8").split("\n")) {
    if (line.startsWith("[[artifact]]")) { cur = {}; continue; }
    const m = /^(name|cid|sha256) = "([^"]*)"/.exec(line);
    if (cur && m) { cur[m[1]] = m[2]; if (m[1] === "name") registry[m[2]] = cur; } } }
const sat = registry[SAT];
check(!!sat, `${SAT} is registered in silmaril/artifacts.toml`);
if (!sat) process.exit(1);

// The static theorem map, read from the view's source.
{ const src = fs.readFileSync(path.join(repo, "tools/silmaril-project/src/project/explore/views/acceptors.js"), "utf8");
  const claims = [...src.matchAll(/sha256: "([0-9a-f]{64})", name: "([^"]+)"/g)].map((m) => ({ sha: m[1], name: m[2] }));
  check(claims.some((c) => c.name === SAT && c.sha === sat.sha256), "the theorem map names the registered SAT component's SHA-256");
  for (const c of claims) if (registry[c.name]) check(registry[c.name].sha256 === c.sha, `theorem map: ${c.name} has its registered SHA-256`);
  for (const m of src.matchAll(/decl: "([^"]+)", module: "([^"]+)"/g)) {
    const file = path.join(repo, m[2].replace(/\./g, "/") + ".lean");
    if (!fs.existsSync(file)) { console.log(`skip ${m[1]}: ${m[2]} is not on this branch`); continue; }
    const short = m[1].split(".").pop();
    check(new RegExp(`^theorem ${short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "m").test(fs.readFileSync(file, "utf8")),
      `${m[2]} states ${short}`);
  } }

// The site's report is the committed one.
const committed = fs.readFileSync(path.join(repo, "tools/wasm-acceptor-harness/report.json"));
const served = path.join(site, "acceptor-runs.json");
check(fs.existsSync(served) && Buffer.compare(fs.readFileSync(served), committed) === 0,
  "the site's acceptor-runs.json is tools/wasm-acceptor-harness/report.json byte for byte");
const report = JSON.parse(committed);

// Fixture sites next to each other under one server root: real (the site's own report),
// fixture, missing, malformed.
const root = fs.mkdtempSync(path.join(os.tmpdir(), "acceptor-runs-"));
const slug = SAT;   // wasm-pages: the registered name (no character outside [A-Za-z0-9._-])
function mkSite(name, runs) {
  const d = path.join(root, name);
  fs.mkdirSync(path.join(d, "wasm/c"), { recursive: true });
  for (const f of ["index.html", "project.sqlite", "explore-sw.js", "wasm/index.json"])
    if (fs.existsSync(path.join(site, f))) fs.copyFileSync(path.join(site, f), path.join(d, f));
  fs.copyFileSync(path.join(site, "wasm/c", slug + ".json"), path.join(d, "wasm/c", slug + ".json"));
  if (runs != null) fs.writeFileSync(path.join(d, "acceptor-runs.json"), runs);
}
const art = report.artifacts.find((a) => a.sha256 === sat.sha256);
check(!!art && art.cid === sat.cid, "the committed report runs the registered SAT bytes (same SHA-256 and CID)");
const base = { suite: "fx", artifact: "sat", sha256: sat.sha256, cid: sat.cid, export: "check-stream",
  params: ["problem: list<s32>", "model: list<s32>"], note: "" };
const fixture = Object.assign({}, report, { command: ["fixture"], artifacts: [art, Object.assign({}, art, { id: "fx/other",
  sha256: "0".repeat(64), cid: "bafkr4iother" })], cases: [
  Object.assign({}, base, { name: "fx-match", class: "positive", args: [[1, 0], [1]], expected: "accepted", observed: { outcome: "accepted" }, verdict: "pass" }),
  Object.assign({}, base, { name: "fx-mismatch", class: "negative", args: [[1, 0], [-1]], expected: "rejected", observed: { outcome: "accepted" }, verdict: "fail" }),
  Object.assign({}, base, { name: "fx-unchecked", class: "", args: [{ $repeat: 1, count: 100000 }, []], expected: null, observed: { outcome: "trap", detail: "wasm trap: unreachable" }, verdict: "unchecked" }),
  Object.assign({}, base, { name: "fx-other-bytes", sha256: "0".repeat(64), cid: "bafkr4iother", args: [[], []], expected: "accepted", observed: { outcome: "accepted" }, verdict: "pass" })],
  summary: { pass: 2, fail: 1, unchecked: 1 } });
mkSite("real", committed);
mkSite("fixture", JSON.stringify(fixture));
mkSite("missing", null);
mkSite("malformed", "{ not json");

const port = 8811;
const srv = spawn("python3", ["-I", path.join(here, "pages_server.py"), "--root", root, "--port", String(port),
  "--log", path.join(os.tmpdir(), "acceptor_runs_requests.jsonl")], { stdio: "ignore" });
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 900 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const open = async (dir, hash) => {
    await p.goto(`http://127.0.0.1:${port}/${dir}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: true }); } };
  // What the section shows: its text, rows, badges and classes.
  const section = () => p.evaluate(() => {
    const s = document.querySelector("section[data-section='acceptor-evidence']");
    if (!s) return null;
    const rows = [...s.querySelectorAll("table.obs-cases tbody tr")].map((r) => ({ name: r.dataset.case, verdict: r.dataset.verdict,
      text: r.textContent, green: !!r.querySelector(".prov-lean, .st-ok, .holds") }));
    const obsTable = s.querySelector("table.obs-cases");
    return { text: s.textContent, rows, err: !!s.querySelector(".err"), none: !!s.querySelector(".obs-none"),
      obsGreen: !!(obsTable && obsTable.querySelector(".prov-lean, .st-ok, .holds, .st")),
      claim: (s.querySelector("[data-claim]") || {}).textContent || null,
      sourceLinks: [...s.querySelectorAll("table.claims a[href^='#/source/']")].map((a) => decodeURIComponent(a.getAttribute("href").slice(9))),
      pageH2: [...document.querySelectorAll("main h2")].map((h) => h.textContent) };
  });
  const pages = [["component", "/wasm-component/" + encodeURIComponent(slug)], ["artifact", "/artifact/" + sat.cid]];

  for (const [what, hash] of pages) {
    await open("real", hash);
    const s = await section();
    const n = report.cases.filter((c) => c.sha256 === sat.sha256).length;
    check(s && s.rows.length === n && n > 0, `real ${what} page: one row per case of the SAT bytes (${s && s.rows.length} of ${n})`);
    check(s && s.rows.every((r) => r.verdict === "pass"), `real ${what} page: every committed case matches its expectation`);
    await shot("acceptor-runs-real-" + what);

    await open("fixture", hash);
    const f = await section();
    check(!!f, `fixture ${what} page: the section is shown`);
    if (!f) continue;
    check(f.text.includes("Runtime observations (Wasmtime 50.0.0) — tested, not proved"), `fixture ${what}: the observations heading names the engine and says tested, not proved`);
    check(f.text.includes(sat.sha256) && f.text.includes(sat.cid), `fixture ${what}: the exact SHA-256 and CID`);
    check(f.text.includes("cranelift") && f.text.includes("nan_canonicalization"), `fixture ${what}: the engine configuration`);
    check(f.rows.map((r) => r.name).join() === "fx-match,fx-mismatch,fx-unchecked", `fixture ${what}: the cases of these bytes only (${f.rows.map((r) => r.name)})`);
    const row = (k) => f.rows.find((r) => r.name === k) || { text: "" };
    check(row("fx-match").verdict === "pass" && row("fx-match").text.includes("matches expectation (test)"), `fixture ${what}: a met expectation reads "matches expectation (test)"`);
    check(row("fx-mismatch").verdict === "fail" && /mismatch: expected rejected/.test(row("fx-mismatch").text), `fixture ${what}: a mismatch is marked`);
    check(row("fx-unchecked").verdict === "unchecked" && row("fx-unchecked").text.includes("no expectation") && !row("fx-unchecked").text.includes("matches"),
      `fixture ${what}: a missing expectation is neutral`);
    check(row("fx-unchecked").text.includes("[1 × 100000]"), `fixture ${what}: a repeated argument is abbreviated`);
    check(row("fx-match").text.includes("check-stream(problem: list<s32>, model: list<s32>)"), `fixture ${what}: the export with its typed signature`);
    check(!f.obsGreen, `fixture ${what}: no proof or status style in the observations table`);
    check(f.claim === "component-level soundness (kernel-checked)", `fixture ${what}: the claim kind (${f.claim})`);
    check(["Silmaril.Project.WasmComponents.SatAccept.checkStream_sound_of_bytes", "Silmaril.Project.WasmComponents.SatAccept.checkNested_sound_of_bytes"]
      .every((d) => f.sourceLinks.includes(d)), `fixture ${what}: the theorems link to their source pages`);
    check(!f.err, `fixture ${what}: no error`);
    await shot("acceptor-runs-fixture-" + what);

    await open("missing", hash);
    const m = await section();
    check(m && m.none && !m.err && /No runtime observations/.test(m.text) && m.rows.length === 0, `no report, ${what}: a neutral notice, no error`);
    check(m && m.claim === "component-level soundness (kernel-checked)", `no report, ${what}: the theorems are still shown`);

    await open("malformed", hash);
    const x = await section();
    check(x && x.err && /acceptor-runs\.json is not JSON/.test(x.text), `malformed report, ${what}: an error in the section's block`);
    check(x && x.pageH2.length > 1, `malformed report, ${what}: the rest of the page renders (${x && x.pageH2.length} headings)`);
  }
  check(errors.length === 0, `no page errors (${errors.join("; ")})`);
} finally {
  await b.close();
  srv.kill();
  fs.rmSync(root, { recursive: true, force: true });
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all passed");
