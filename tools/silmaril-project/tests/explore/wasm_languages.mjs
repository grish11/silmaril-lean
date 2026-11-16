// Languages on the Wasm tab, in Chromium: a module that wasm-pages built from a Lean value has no
// CID, only the SHA-256 of its encoded bytes. When a registered artifact has exactly those bytes and
// a language is registered over it (`op := artifact`, a CID-pinned value and an interpretation, as
// `silmaril language … (op := artifact)` records them), the module's page shows that language
// with a link to its Languages page; a module whose bytes are not registered shows nothing.
//
// The registration is SYNTHETIC: this test copies the site and adds the rows the registry would
// write (artifact, value source, language) to the copy's database, for the first Lean-built
// module of the site that has a SHA-256 and whose bytes are served. It checks the rendering only.
//   node wasm_languages.mjs SITE_DIR [SHOTS_DIR]   (a `make pages` output: index.html, project.sqlite, wasm/)
import { spawn, execFileSync } from "node:child_process";
import crypto from "node:crypto";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const work = fs.mkdtempSync(path.join(os.tmpdir(), "explore-wasm-languages-"));
const root = path.join(work, "site");
fs.cpSync(site, root, { recursive: true, dereference: true });
const idx = JSON.parse(fs.readFileSync(path.join(root, "wasm", "index.json"), "utf8"));
const page = (slug) => { const f = path.join(root, "wasm", "m", slug + ".json"); return fs.existsSync(f) ? JSON.parse(fs.readFileSync(f, "utf8")) : null; };
const leanBuilt = idx.modules.map((m) => [m.slug, page(m.slug)]).filter(([s, d]) => d && !d.summary.source.cid && d.summary.source.sha256 &&
  fs.existsSync(path.join(root, "wasm", "blob", s + ".wasm")));
if (leanBuilt.length === 0) { console.log("skip no Lean-built module with a SHA-256 and served bytes"); process.exit(0); }
const [slug, data] = leanBuilt[0];
const other = leanBuilt[1];
const bytes = fs.readFileSync(path.join(root, "wasm", "blob", slug + ".wasm"));
const sha = crypto.createHash("sha256").update(bytes).digest("hex");
check(sha === data.summary.source.sha256, `${slug}: the served bytes have the page's SHA-256`);
const cid = "bafkr4isyntheticwasmlanguagestest" + sha.slice(0, 20);
execFileSync("python3", ["-I", "-c", `
import sqlite3, sys, json
db, sha, cid, size = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
c = sqlite3.connect(db)
def cols(t): return [r[1] for r in c.execute("pragma table_info(%s)" % t)]
def put(t, row):
    k = [x for x in cols(t)]
    vals = [row.get(x) for x in k]
    c.execute("insert into %s (%s) values (%s)" % (t, ",".join(k), ",".join("?" * len(k))), vals)
interp = c.execute("select name from language_interpretations order by name limit 1").fetchone()[0]
dom = c.execute("select domain from language_interpretations where name = ?", (interp,)).fetchone()[0]
put("artifacts", dict(sid="f" * 64, cid=cid, type="blob", name="test.synthetic.wasm_bytes", size=size, sha256=sha, git_sha1="0" * 40, registry="synthetic"))
put("value_sources", dict(value="test.synthetic.wasm_value", pos=0, cid=cid, format="test", decl="Test.value", obligation="test.synthetic.parses"))
ident = json.dumps({"op": "artifact", "synthetic": True})
put("languages", dict(sid="d" * 64, name="test.synthetic.wasm_language", domain=dom, op="artifact", decl="Test.lang", carrier="Set T",
    title="synthetic language over the module's bytes", value="test.synthetic.wasm_value", interpretation=interp,
    identity=ident, identity_hash="c" * 64, module="Test", origin="local"))
c.commit()
print(interp)
`, path.join(root, "project.sqlite"), sha, cid, String(bytes.length)]);
const port = 8801;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", root, "--port", String(port), "--log", path.join(work, "requests.jsonl")], { stdio: "ignore" });
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 900 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const settle = () => p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  await p.goto(`http://127.0.0.1:${port}/index.html?load=full#/wasm-module/${encodeURIComponent(slug)}`);
  await settle();
  const sec = await p.evaluate(() => { const s = document.querySelector("section[data-section=languages]");
    return s && { text: s.innerText, links: [...s.querySelectorAll("a")].map((a) => a.getAttribute("href")) }; });
  check(!!sec && sec.links.includes("#/language/test.synthetic.wasm_language") && /synthetic language/.test(sec.text),
    `${slug}: the module page shows the language registered over its bytes, linked to Languages`);
  if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.locator("section[data-section=languages]").screenshot({ path: path.join(shots, "wasm-languages.png") }).catch(() => {}); }
  await p.click("section[data-section=languages] a[href='#/language/test.synthetic.wasm_language']");
  await settle();
  check(await p.evaluate(() => window.explore.view === "language"), "the link opens the language's page");
  if (other) {
    await p.evaluate((h) => { location.hash = h; }, "#/wasm-module/" + encodeURIComponent(other[0]));
    await settle();
    check(await p.evaluate(() => !document.querySelector("section[data-section=languages]")), `${other[0]}: unregistered bytes show no languages`);
  }
  check(errors.length === 0, "no page errors " + errors.join("; "));
} finally {
  await b.close(); srv.kill();
  fs.rmSync(work, { recursive: true, force: true });
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all ok");
