// The acceptor modules of Silmaril.Wasi.Accept.Catalog.concreteModules on the explorer's Wasm tab,
// in Chromium, on a `make pages` output:
// * each is listed on #/wasm and its module page opens, with its exports;
// * the page data names the Lean declaration (the proof target is that module AST) and says how
//   the bytes were encoded (encodeModule?, encodeModule?_sound);
// * the SHA-256 that wasm-pages computed in Lean equals the SHA-256 of the served .wasm, both as
//   computed here and as the page's "SHA-256 of the download" button computes it in the browser;
// * the bytes are valid (the Lean validator, check_ok_iff).
//   node wasm_acceptors.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import crypto from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8798;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "wasm_acceptors_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
// The catalog's concrete modules: slug, Lean declaration, export to expect.
const modules = [
  ["silmaril.wasm.examples.json_accept.prog", "Silmaril.Wasm.Examples.JsonAccept.prog", "accept"],
  ["silmaril.wasm.game.examples.ex_start", "Silmaril.Wasm.Game.Examples.exStart", "run"]];
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 900 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const open = async (hash) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png") }); } };
  await open("/wasm");
  await p.waitForSelector("h2");
  const listed = await p.evaluate(() => [...document.querySelectorAll("a[href^='#/wasm-module/']")].map((a) => decodeURIComponent(a.getAttribute("href").slice(14))));
  for (const [slug, decl, exp] of modules) {
    check(listed.includes(slug), `#/wasm lists ${slug}`);
    const d = JSON.parse(fs.readFileSync(path.join(site, "wasm/m", slug + ".json")));
    const src = d.summary.source;
    check(src.kind === "lean" && src.name === decl, `${slug}: source is the Lean value ${decl} (${src.kind} ${src.name})`);
    check(/encodeModule\?/.test(src.doc) && /encodeModule\?_sound/.test(src.doc), `${slug}: the encoding and its soundness theorem are named`);
    const bytes = fs.readFileSync(path.join(site, "wasm/blob", slug + ".wasm"));
    const h = crypto.createHash("sha256").update(bytes).digest("hex");
    check(src.sha256 === h, `${slug}: Lean SHA-256 ${src.sha256} = SHA-256 of the served bytes (${bytes.length} B)`);
    const v = d.validity || d.summary.validity || {};
    check(v.status === "valid", `${slug}: the bytes are valid (${v.status})`);
    await open("/wasm-module/" + encodeURIComponent(slug));
    const text = await p.evaluate(() => document.querySelector("main") ? document.querySelector("main").textContent : document.body.textContent);
    check(text.includes(exp), `${slug}: the module page shows the export ${exp}`);
    await p.click("#wsha");
    await p.waitForFunction(() => /^[0-9a-f]{64}/.test(document.querySelector("#wshaout").textContent), null, { timeout: 30000 });
    const browserSha = await p.evaluate(() => document.querySelector("#wshaout code").textContent);
    check(browserSha === src.sha256, `${slug}: the browser's SHA-256 of the download equals the Lean one`);
    await shot("wasm-acceptor-" + slug);
  }
  check(errors.length === 0, `no page errors (${errors.join("; ")})`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all passed");
