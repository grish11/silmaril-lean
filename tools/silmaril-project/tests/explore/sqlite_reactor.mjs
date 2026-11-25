import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const { chromium } = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]);
const shots = process.argv[3] ? path.resolve(process.argv[3]) : null;
const work = fs.mkdtempSync(path.join(os.tmpdir(), "reactor-browser-"));
const index = JSON.parse(fs.readFileSync(path.join(site, "wasm/index.json")));
const reactor = index.modules.find((module) => module.source.name === "sqlite.wasi.preview1.reactor");
assert.ok(reactor, "pinned reactor is listed in Wasm Explorer");
const { slug } = reactor;
assert.equal(slug, `sqlite.wasi.preview1.reactor.${reactor.source.sha256}`);
const inventory = JSON.parse(fs.readFileSync(path.join(site, "wasm", "m", `${slug}.json`)));
const port = 8790 + process.pid % 400;
const base = `http://127.0.0.1:${port}/index.html`;
const server = spawn("python3", ["-I", fileURLToPath(new URL("pages_server.py", import.meta.url)),
  "--root", site, "--port", String(port), "--log", path.join(work, "requests.jsonl")], { stdio: "inherit" });
let browser;
try {
  for (let i = 0; ; i++) {
    if (await fetch(base, { method: "HEAD" }).then((response) => response.ok, () => false)) break;
    if (i === 49) throw new Error("Reactor browser test server did not start");
    await new Promise((resolve) => setTimeout(resolve, 100));
  }
  const localChrome = "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
  browser = await chromium.launch({ executablePath: process.env.CHROME || (fs.existsSync(localChrome) ? localChrome : undefined) });
  const page = await browser.newPage({ viewport: { width: 1440, height: 960 } });
  const details = [], errors = [];
  page.on("pageerror", (e) => errors.push(e.message));
  page.on("request", (r) => {
    const part = new URL(r.url()).pathname;
    if (part.startsWith(`/wasm/f/${slug}/`)) details.push(part);
  });
  const shot = async (name) => {
    if (!shots) return;
    fs.mkdirSync(shots, { recursive: true });
    await page.screenshot({ path: path.join(shots, name + ".png") });
  };
  const checkLlvmLink = async (slot, symbol) => {
    const llvm = page.getByRole("link", { name: "LLVM build provenance" });
    const source = JSON.parse((await page.locator("#source-meta").textContent()) || "null");
    const hasReceipt = inventory.llvmReceipt?.symbols?.[slot] === symbol;
    const expected = process.env[`SQLITE_REACTOR_LLVM_${slot}`];
    if (expected) assert.equal(hasReceipt ? "present" : "absent", expected);
    assert.equal(await llvm.count(), source && hasReceipt ? 1 : 0);
    if (source && hasReceipt) {
      assert.equal(await llvm.getAttribute("href"),
        `${source.repo}/blob/${source.rev}/tools/sqlite-wasm/llvm-provenance/receipt.json`);
      assert.ok((await page.locator("#main").innerText()).includes(`early bitcode symbol ${symbol}`));
    }
  };

  await page.goto(`${base}#/wasm`);
  await page.locator("#wfq").fill("sqlite3_libversion_number");
  const result = page.locator("#wfl").getByRole("link", { name: "sqlite3_libversion_number", exact: true });
  await result.waitFor();
  assert.equal(await result.getAttribute("href"), `#/wasm-func/${slug}/289`);
  assert.deepEqual(details, []);
  await result.click();
  await page.locator("#wcy").waitFor();
  assert.match(await page.locator("#main").innerText(), /SqliteWasm\.version_exec/);
  await checkLlvmLink(289, "sqlite3_libversion_number");
  assert.deepEqual(details, [`/wasm/f/${slug}/289.json`]);

  const openModule = async () => {
    await page.goto(`${base}#/wasm-module/${slug}`);
    await page.locator("#reactor-function-query").waitFor();
  };
  const openSlot = async (query) => {
    await page.locator("#reactor-function-query").fill(query);
    await page.locator("#reactor-functions").getByRole("link").click();
  };
  await openModule();
  assert.match(await page.locator("#main").innerText(), /1556 slots · 23 imported · 1533 defined/);
  assert.match(await page.locator("#main").innerText(), /SqliteWasm\.originalDecode/);
  assert.equal(await page.locator("#reactor-function-count").innerText(), "1556 of 1556 slots (first 100 shown)");
  assert.equal(details.length, 1);
  await shot("reactor-inventory");
  await openSlot("sqlite3GetVarint32");
  await page.locator("#wcy").waitFor();
  assert.match(await page.locator("#main").innerText(), /107791, 180 bytes/);
  assert.deepEqual(details, [289, 231].map((slot) => `/wasm/f/${slug}/${slot}.json`));
  await shot("reactor-varint32-cfg");

  await openModule();
  await openSlot("434");
  await page.locator("#wcy").waitFor();
  assert.match(await page.locator("#main").innerText(), /SqliteWasm\.getVarint_oneByte/);
  await openModule();
  await openSlot("0");
  await page.getByText(/Imported function/).waitFor();
  await openModule();
  await openSlot("1555");
  await page.getByText(/Detailed CFG was omitted/).waitFor();
  assert.deepEqual(details, [289, 231, 434].map((slot) => `/wasm/f/${slug}/${slot}.json`));

  await openModule();
  await openSlot("530");
  await page.locator("#wcy").waitFor();
  assert.equal(await page.getByRole("link", { name: "SqliteWasm.putVarint_oneByte" }).count(), 1);
  await checkLlvmLink(530, "sqlite3PutVarint");
  const effects = await page.locator("#main dt").filter({ hasText: /^effect marks$/ })
    .evaluate((term) => term.nextElementSibling.textContent.split(", "));
  assert.deepEqual(new Set(effects), new Set(["may-trap", "call"]));
  assert.equal(details.at(-1), `/wasm/f/${slug}/530.json`);

  const exitOnly = { idx: 530, wat: "(func)", cfg: { blocks: [], edges: [], entry: "exit" } };
  for (const payload of [null, { idx: 530, cfg: {} }, { idx: 530, wat: "(func)", cfg: {} }, exitOnly]) {
    const broken = await browser.newPage();
    broken.on("pageerror", (e) => errors.push(e.message));
    await broken.route(`**/wasm/f/${slug}/530.json`, (route) =>
      route.fulfill({ contentType: "application/json", body: JSON.stringify(payload) }));
    await broken.goto(`${base}#/wasm-func/${slug}/530`);
    await broken.getByText("The detail file did not contain a usable CFG for this slot.").waitFor();
    assert.match(await broken.locator("#main h2").innerText(), /sqlite3PutVarint/);
    assert.ok((await broken.locator("#main").innerText()).includes(reactor.source.sha256));
    const link = broken.getByRole("link", { name: "SqliteWasm.putVarint_oneByte" });
    assert.match(await link.getAttribute("href"), /\/PutVarintCheck\.lean$/);
    assert.equal(await broken.locator("#wcy").count(), 0);
    await broken.close();
  }
  const empty = await browser.newPage();
  empty.on("pageerror", (e) => errors.push(e.message));
  const emptyInventory = structuredClone(inventory);
  emptyInventory.functions[530].blocks = 0;
  emptyInventory.functions[530].instrs = 0;
  await empty.route(`**/wasm/m/${slug}.json`, (route) => route.fulfill({ json: emptyInventory }));
  await empty.route(`**/wasm/f/${slug}/530.json`, (route) => route.fulfill({ json: exitOnly }));
  await empty.goto(`${base}#/wasm-func/${slug}/530`);
  await empty.locator("#wcy").waitFor();
  assert.equal(await empty.locator("#wlegend [data-c=flow]").innerText(), "0");
  assert.equal(await empty.locator("#main .err").count(), 0);
  await empty.close();
  assert.deepEqual(errors, []);
  console.log("SQLite reactor search, lazy CFGs, effect marks, and provenance-preserving detail errors passed.");
} finally {
  await browser?.close();
  server.kill();
  fs.rmSync(work, { recursive: true, force: true });
}
