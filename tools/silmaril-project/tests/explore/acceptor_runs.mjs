// The acceptor-evidence section (explore/views/acceptors.js) in Chromium, on a `make pages` output
// and on fixtures built from it:
// * the site's acceptor-runs.json is the committed harness report, byte for byte
//   (tools/wasm-acceptor-harness/report.json, copied by `make pages`), and the SAT component's
//   page lists every case the report runs on its SHA-256;
// * fixture report (a match, a mismatch, a case without expectation, an expected detail met and
//   missed, a case of other bytes, a claim for these bytes): the component and artifact pages show
//   "Runtime observations (Wasmtime 50.0.0) — tested, not proved", the exact CID and SHA-256, one
//   row per case of these bytes only, the verdicts as "matches expectation (test)" / "mismatch" /
//   "no expectation", and no proof (green) style on any observation; the Lean theorems are read
//   from the report's claims and shown apart, with their kind of claim;
// * claims: a report without claims (v2 with none, and a v1 report) names no theorem; a claim whose
//   SHA-256 is not the artifact's (a mismatched sha) is not shown; a withheld claim is noted;
// * no report: a neutral notice on the component page and no error, nothing on the artifact page;
// * a malformed report: an error in the section's own block, the rest of the page rendered;
// * the suites' claims (in the committed report): every claim's SHA-256 is its artifact's and,
//   when registered (SAT must be), its registered one; every named theorem whose header is on this
//   branch is stated in it.
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

// The claims, read from the committed report (the harness copies them from the suite files).
const committed = fs.readFileSync(path.join(repo, "tools/wasm-acceptor-harness/report.json"));
const report = JSON.parse(committed);
check(report.kind === "silmaril.wasm-acceptor-harness.report/v2", `the committed report is v2 (${report.kind})`);
{ const claims = report.artifacts.flatMap((a) => (a.claims || []).map((c) => Object.assign({ art: a }, c)));
  check(claims.some((c) => c.registry_name === SAT && c.sha256 === sat.sha256), "the report claims about the registered SAT component's SHA-256");
  for (const c of claims) {
    check(c.sha256 === c.art.sha256 && c.art.pinned_sha256_ok === true, `claim on ${c.art.id}: made for the artifact's own (pinned) SHA-256`);
    if (c.registry_name && registry[c.registry_name]) check(registry[c.registry_name].sha256 === c.sha256, `claim: ${c.registry_name} has its registered SHA-256`);
  }
  for (const t of claims.flatMap((c) => c.theorems)) {
    const file = path.join(repo, t.module.replace(/\./g, "/") + ".lean");
    if (!fs.existsSync(file)) { console.log(`skip ${t.decl}: ${t.module} is not on this branch`); continue; }
    const short = t.decl.split(".").pop();
    check(new RegExp(`^theorem ${short.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "m").test(fs.readFileSync(file, "utf8")),
      `${t.module} states ${short}`);
  } }

// The site's report is the committed one.
const served = path.join(site, "acceptor-runs.json");
check(fs.existsSync(served) && Buffer.compare(fs.readFileSync(served), committed) === 0,
  "the site's acceptor-runs.json is tools/wasm-acceptor-harness/report.json byte for byte");

// Fixture sites next to each other under one server root: real (the site's own report),
// fixture, no claims (v2), v1, mismatched claim, withheld claim, missing, malformed.
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
const satClaim = art.claims.find((c) => c.registry_name === SAT);
const claim = Object.assign({}, satClaim, { kind: "fixture claim kind", level: "core-module", scope: "fixture scope",
  value: "Fixture.bytes", theorems: [{ decl: "Fixture.check_sound", module: "Fixture.Thms", states: "fixture statement" }] });
const fixture = Object.assign({}, report, { command: ["fixture"], artifacts: [Object.assign({}, art, { claims: [satClaim, claim] }),
  Object.assign({}, art, { id: "fx/other", sha256: "0".repeat(64), cid: "bafkr4iother", claims: [] })], cases: [
  Object.assign({}, base, { name: "fx-match", class: "positive", args: [[1, 0], [1]], expected: "accepted", observed: { outcome: "accepted" }, verdict: "pass" }),
  Object.assign({}, base, { name: "fx-mismatch", class: "negative", args: [[1, 0], [-1]], expected: "rejected", observed: { outcome: "accepted" }, verdict: "fail" }),
  Object.assign({}, base, { name: "fx-unchecked", class: "", args: [{ $repeat: 1, count: 100000 }, []], expected: null, observed: { outcome: "trap", detail: "wasm trap: unreachable" }, verdict: "unchecked" }),
  Object.assign({}, base, { name: "fx-detail-met", class: "malformed", args: [[], []], expected: "trap", expected_detail: "unreachable",
    observed: { outcome: "trap", detail: "wasm trap: wasm `unreachable` instruction executed" }, verdict: "pass" }),
  Object.assign({}, base, { name: "fx-detail-missed", class: "malformed", args: [[], []], expected: "trap", expected_detail: "out of bounds",
    observed: { outcome: "trap", detail: "wasm trap: wasm `unreachable` instruction executed" }, verdict: "fail" }),
  Object.assign({}, base, { name: "fx-other-bytes", sha256: "0".repeat(64), cid: "bafkr4iother", args: [[], []], expected: "accepted", observed: { outcome: "accepted" }, verdict: "pass" })],
  summary: { pass: 3, fail: 2, unchecked: 1 } });
// The same observations with no claims (v2), as a v1 report (no claims field), with a claim made
// for other bytes than the artifact's, and with a withheld claim.
const noClaims = Object.assign({}, fixture, { artifacts: fixture.artifacts.map((a) => Object.assign({}, a, { claims: [] })) });
const v1 = Object.assign({}, fixture, { kind: "silmaril.wasm-acceptor-harness.report/v1",
  artifacts: fixture.artifacts.map((a) => { const b = Object.assign({}, a); delete b.claims; return b; }) });
delete v1.suites;
const mismatched = Object.assign({}, fixture, { artifacts: [Object.assign({}, art, { claims: [Object.assign({}, satClaim, { sha256: "1".repeat(64) })] }),
  Object.assign({}, art, { id: "fx/one", sha256: "1".repeat(64), cid: "bafkr4ione", claims: [satClaim] })] });
const withheld = Object.assign({}, noClaims, { artifacts: [Object.assign({}, art, { claims: [], claims_withheld: "1 claim(s) withheld: the file is not the pinned SHA-256" })] });
mkSite("real", committed);
mkSite("fixture", JSON.stringify(fixture));
mkSite("noclaims", JSON.stringify(noClaims));
mkSite("v1", JSON.stringify(v1));
mkSite("mismatched", JSON.stringify(mismatched));
mkSite("withheld", JSON.stringify(withheld));
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
      claims: [...s.querySelectorAll("[data-claim]")].map((e) => ({ kind: e.textContent, level: e.dataset.claim, cls: e.className })),
      claimsNone: !!s.querySelector(".claims-none"),
      decls: [...s.querySelectorAll("table.claims td:first-child code")].map((c) => c.textContent),
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
    check(f.rows.map((r) => r.name).join() === "fx-match,fx-mismatch,fx-unchecked,fx-detail-met,fx-detail-missed", `fixture ${what}: the cases of these bytes only (${f.rows.map((r) => r.name)})`);
    const row = (k) => f.rows.find((r) => r.name === k) || { text: "" };
    check(row("fx-match").verdict === "pass" && row("fx-match").text.includes("matches expectation (test)"), `fixture ${what}: a met expectation reads "matches expectation (test)"`);
    check(row("fx-mismatch").verdict === "fail" && /mismatch: expected rejected/.test(row("fx-mismatch").text), `fixture ${what}: a mismatch is marked`);
    check(row("fx-unchecked").verdict === "unchecked" && row("fx-unchecked").text.includes("no expectation") && !row("fx-unchecked").text.includes("matches"),
      `fixture ${what}: a missing expectation is neutral`);
    check(row("fx-detail-met").verdict === "pass" && row("fx-detail-met").text.includes("detail contains unreachable"), `fixture ${what}: a met expected detail passes`);
    check(row("fx-detail-missed").verdict === "fail" && /mismatch: detail lacks "out of bounds"/.test(row("fx-detail-missed").text), `fixture ${what}: a missed expected detail is a mismatch`);
    check(row("fx-unchecked").text.includes("[1 × 100000]"), `fixture ${what}: a repeated argument is abbreviated`);
    check(row("fx-match").text.includes("check-stream(problem: list<s32>, model: list<s32>)"), `fixture ${what}: the export with its typed signature`);
    check(!f.obsGreen, `fixture ${what}: no proof or status style in the observations table`);
    check(f.claim === "component-level soundness (kernel-checked)", `fixture ${what}: the claim kind (${f.claim})`);
    check(f.claims.length === 2 && f.claims[1].kind === "fixture claim kind" && f.claims[1].level === "core-module" && !/prov-lean/.test(f.claims[1].cls),
      `fixture ${what}: every claim of the report is shown, a core-module claim without the component style`);
    check(f.decls.includes("Fixture.check_sound") && f.text.includes("Fixture.bytes") && f.text.includes(sat.sha256), `fixture ${what}: the claim's theorems, value and SHA-256`);
    check(["Silmaril.Project.WasmComponents.SatAccept.checkStream_sound_of_bytes", "Silmaril.Project.WasmComponents.SatAccept.checkNested_sound_of_bytes"]
      .every((d) => f.sourceLinks.includes(d)), `fixture ${what}: the theorems link to their source pages`);
    check(!f.err, `fixture ${what}: no error`);
    await shot("acceptor-runs-fixture-" + what);

    for (const [dir, label] of [["noclaims", "a v2 report without claims"], ["v1", "a v1 report"], ["mismatched", "a claim made for other bytes"]]) {
      await open(dir, hash);
      const c = await section();
      check(c && c.rows.length === 5 && !c.err, `${label}, ${what}: the observations are shown`);
      check(c && c.claims.length === 0 && c.decls.length === 0 && c.claimsNone, `${label}, ${what}: no theorem is named`);
      check(c && !c.obsGreen, `${label}, ${what}: no proof style in the observations`);
    }
    await open("withheld", hash);
    const w = await section();
    check(w && w.claims.length === 0 && /claim\(s\) withheld/.test(w.text), `withheld claim, ${what}: noted, not shown`);

    await open("missing", hash);
    const m = await section();
    if (what === "component") {
      check(m && m.none && !m.err && /No runtime observations or claims/.test(m.text) && m.rows.length === 0, `no report, ${what}: a neutral notice, no error`);
      check(m && m.claims.length === 0, `no report, ${what}: no theorem is named`);
    } else check(m === null, `no report, ${what}: no section`);

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
