// The Languages view and the artifact section, in Chromium, on a `make pages` output:
// * #/languages lists the registered languages from the database (every row of `languages`) and
//   its domain filter narrows the list;
// * a format profile's page shows its membership examples with the shared status badges, an
//   expected negative result (CSA) is not marked as a failure, and the identity is shown;
// * the self-test's Wasm language links to its interpretation's definition, ABI and environment,
//   and the artifact page of its CID carries the "Languages" section linking back to it;
// * no page shows an error, and no page error is raised.
//   node languages.mjs SITE_DIR [SHOTS_DIR]   (SITE_DIR holds index.html and project.sqlite)
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8799;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "languages_requests.jsonl")], { stdio: "ignore" });
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
  const go = async (hash) => { await p.evaluate((h) => { location.hash = h; }, hash); await settle(); };
  const errs = () => p.evaluate(() => [...document.querySelectorAll("#main .err")].map((e) => e.textContent.slice(0, 200)));
  const shot = async (n) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, n), fullPage: false }); } };
  await p.goto(`http://127.0.0.1:${port}/index.html#/languages`);
  await settle();

  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav.includes("#/languages"), "the Languages view is in the navigation");
  const rows = await p.evaluate(() => document.querySelectorAll("#languages-table tbody tr").length);
  check(rows > 0, `#/languages lists ${rows} languages`);
  const heads = await p.evaluate(() => [...document.querySelectorAll("#languages-table thead th")].map((t) => t.textContent));
  check(!heads.includes("operands"), `the index has no operands column: ${heads.join(", ")}`);
  // the Wasm language has one open problem with expect OPN: no expectation, so never "all met"
  const wasmAgg = await p.evaluate(() => { const r = [...document.querySelectorAll("#languages-table tbody tr")].find((r) => r.textContent.includes("silmaril.selftest.lang.wasm.accept"));
    const e = r && r.querySelector("[data-expectations]"); return e && e.dataset.expectations; });
  check(wasmAgg === "incomplete", `an open problem without an expectation is not met: ${wasmAgg}`);
  await shot("languages.png");

  await go("#/languages/?domain=nat.additive");
  const nat = await p.evaluate(() => [...document.querySelectorAll("#languages-table tbody tr td:first-child")].map((t) => t.textContent.trim()));
  check(nat.length >= 1 && nat.length < rows && nat.every((n) => n.startsWith("silmaril.selftest.lang.evens")), `domain filter: ${nat.join(", ")}`);

  await go("#/language/formats.cbor.drisl.language_atproto_core_exact_cid");
  const ex = await p.evaluate(() => [...document.querySelectorAll("#language-problems tbody tr")].map((r) => ({
    text: r.textContent, st: !!r.querySelector(".st"), bad: !!r.querySelector(".st-bad"), unmet: !!r.querySelector(".st-unmet") })));
  check(ex.length >= 5, `the ATProto-core profile shows ${ex.length} examples`);
  check(ex.every((r) => r.st), "every example carries the shared status badge");
  check(ex.some((r) => /∉/.test(r.text)) && ex.every((r) => !r.bad && !r.unmet), "expected rejections are neither failures nor unmet");
  check(await p.evaluate(() => /Silmaril\.Formats\.Cbor\.Drisl\.Profile\.atprotoCoreExactCid/.test(document.querySelector("#main pre.code").textContent)),
    "the identity names the exact profile");
  await shot("language-atproto.png");
  const agg = await p.evaluate(() => { const e = document.querySelector("#language-expectations [data-expectations]"); return e && e.dataset.expectations; });
  check(agg === "all met", `the profile's expectations: ${agg}`);
  const hex = await p.evaluate(() => [...document.querySelectorAll("#language-problems tbody tr")].map((r) => r.children[1].textContent));
  check(hex.some((t) => /^a2 61 61 01 61 62 82 f5 f6/.test(t) && t.includes(String.raw`b"\xa2aa\x01ab\x82\xf5\xf6" (display)`)),
    "sentences are shown as hex and as an escaped display literal");

  // an intentional negative example: refuted, as expected (the deployed l65 was marked "!")
  await go("#/problem/formats.examples.ascii.l65");
  const l65 = await p.evaluate(() => { const s = document.querySelector("#main h2 .st"); return s && { cls: s.className, code: s.dataset.code, title: s.title }; });
  check(!!l65 && l65.code === "UNS" && !/st-bad|st-unmet/.test(l65.cls), `l65 is UNS as expected: ${l65 && l65.title}`);

  await go("#/language/silmaril.selftest.lang.wasm.accept");
  const w = await p.evaluate(() => document.querySelector("#main dl").textContent);
  check(/acceptBytes32/.test(w) && /Callout\.bytes32/.test(w) && /UEnvOk/.test(w), "the Wasm language names its interpretation, ABI and environment");
  const cid = await p.evaluate(() => { const a = [...document.querySelectorAll("#main dl a")].find((a) => a.getAttribute("href").startsWith("#/artifact/")); return a && decodeURIComponent(a.getAttribute("href").slice(11)); });
  check(!!cid, `the Wasm language links its artifact ${cid}`);
  if (cid) {
    await go("#/artifact/" + encodeURIComponent(cid));
    const sec = await p.evaluate(() => { const s = document.querySelector('section[data-section="languages"]'); return s && [...s.querySelectorAll("a")].map((a) => a.getAttribute("href")); });
    check(!!sec && sec.includes("#/language/silmaril.selftest.lang.wasm.accept"), "the artifact page's Languages section links the language");
    await shot("artifact-languages.png");
  }
  check((await errs()).length === 0, "no error on the pages");
  check(errors.length === 0, "no page errors " + errors.join("; "));
} finally {
  await b.close(); srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all ok");
