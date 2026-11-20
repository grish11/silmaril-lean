// The Containers view (docs/projects/containers-examples.md), in Chromium, on a site built from
// the self-test database (`make project-check`, then `sil project explore`, plus
// `examples/containers/Examples.lean --json SITE/containers-examples.json`, or `make pages`):
// * #/containers lists the examples of the registry group `containers.examples`, in order, with
//   real/model, profile, specification, run and the registry's verdict;
// * the verdicts are the registry's: the no-op, the crash's partial correctness, HTTP and vsock
//   hold; the crash's total correctness and the thread creation fail;
// * an example's page shows image, digests, runtime, machine, clone policy, profile, the proved run,
//   the run computed now, theorems and the registry's shape, arguments and answers;
// * no page error.
//   node containers.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8803;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "containers_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const b = await pw.chromium.launch({ executablePath: process.env.CHROME ||
  (fs.existsSync("/opt/ms-playwright/chromium-1248/chrome-linux64/chrome") ? "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome" : undefined) });
try {
  await new Promise((r) => setTimeout(r, 800));
  const p = await b.newPage({ viewport: { width: 1400, height: 1000 } });
  const errors = [];
  p.on("pageerror", (e) => errors.push(e.message));
  const open = async (hash) => {
    await p.goto(`http://127.0.0.1:${port}/index.html#${hash}`);
    await p.waitForFunction(() => window.explore && window.explore.ready && !window.explore.busy, null, { timeout: 60000 });
  };
  const shot = async (name) => { if (shots) { fs.mkdirSync(shots, { recursive: true }); await p.screenshot({ path: path.join(shots, name + ".png"), fullPage: true }); } };

  await open("/containers");
  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav.includes("#/containers"), "Containers is in the navigation");
  check(await p.evaluate(() => !!document.querySelector("[data-experimental]")), "marked experimental");
  const rows = await p.evaluate(() => [...document.querySelectorAll("#containers-table tbody tr")].map((tr) => ({
    name: tr.dataset.problem, fixture: (tr.querySelector("[data-fixture]") || {}).dataset?.fixture,
    outcome: (tr.querySelector("[data-outcome]") || {}).dataset?.outcome, code: (tr.querySelector("[data-code]") || {}).dataset?.code,
    run: tr.cells[4].textContent.trim(),
    word: (tr.querySelector("[data-verdict]") || {}).textContent, expectation: (tr.querySelector("[data-expectation]") || {}).dataset?.expectation,
    note: (tr.querySelector("[data-note]") || {}).textContent })));
  const names = rows.map((r) => r.name);
  check(JSON.stringify(names) === JSON.stringify(["containers.noop.oci_wp", "containers.http_serve.oci_wlp", "containers.examples.crash_wlp",
    "containers.examples.crash_wp", "containers.mini.thread_spawn_wlp", "containers.examples.http", "containers.examples.vsock"]),
    `the group's examples, in order (${names.join(", ")})`);
  const by = Object.fromEntries(rows.map((r) => [r.name, r]));
  check(by["containers.noop.oci_wp"]?.fixture === "real", "the no-op is real");
  check(by["containers.http_serve.oci_wlp"]?.fixture === "real", "http-serve is real");
  check(["containers.examples.crash_wlp", "containers.mini.thread_spawn_wlp", "containers.examples.http", "containers.examples.vsock"]
    .every((n) => by[n]?.fixture === "model"), "the others are models");
  for (const [n, c] of [["containers.noop.oci_wp", "THM"], ["containers.http_serve.oci_wlp", "THM"], ["containers.examples.crash_wlp", "THM"], ["containers.examples.crash_wp", "UNS"],
    ["containers.mini.thread_spawn_wlp", "UNS"], ["containers.examples.http", "THM"], ["containers.examples.vsock", "THM"]])
    check(by[n]?.code === c, `${n}: registry status ${c} (${by[n]?.code})`);
  check(/UNDEFINED BEHAVIOUR/.test(by["containers.mini.thread_spawn_wlp"]?.run || ""), "the thread example's run is undefined behaviour");
  const heads = await p.evaluate(() => [...document.querySelectorAll("#containers-table thead th")].map((th) => th.textContent.trim()));
  check(heads[1] === "kind" && heads[5] === "verdict", `column headers (${heads.join(" | ")})`);
  for (const n of ["containers.noop.oci_wp", "containers.http_serve.oci_wlp", "containers.examples.crash_wlp", "containers.examples.http", "containers.examples.vsock"])
    check(by[n]?.word === "Proved" && by[n]?.expectation === "met" && by[n]?.note === "as expected", `${n} reads "Proved, as expected" (${by[n]?.word}, ${by[n]?.note})`);
  for (const n of ["containers.examples.crash_wp", "containers.mini.thread_spawn_wlp"])
    check(by[n]?.word === "Refuted" && by[n]?.expectation === "met" && /negative example/.test(by[n]?.note || ""),
      `${n} reads as an expected negative result, not a failure (${by[n]?.word}, ${by[n]?.note})`);
  check(await p.evaluate(() => [...document.querySelectorAll("#containers-table [data-verdict='refuted']")]
    .every((e) => !e.classList.contains("fails"))), "expected refutations are not styled as failures");
  const invisible = await p.evaluate(() => [...document.querySelectorAll("#containers-table [data-verdict]")]
    .filter((e) => { const c = getComputedStyle(e); return c.backgroundColor === "rgba(0, 0, 0, 0)" || c.backgroundColor === c.color; })
    .map((e) => e.textContent));
  check(invisible.length === 0, `every verdict label is visible (${invisible.join(", ")})`);
  check(await p.evaluate(() => !!document.querySelector("#containers-status")), "one details panel says what verdicts rest on");
  await shot("containers");

  await open("/container/containers.noop.oci_wp");
  const detail = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("#container-detail tr")]
    .map((tr) => [tr.cells[0].textContent.trim(), tr.cells[1].textContent.trim()])));
  check(/sha256:f13b70f2cd9336b73436e4c76fd475138a253c140d1a4e2d80dbddd03f2542d8/.test(detail.digests || ""), "the manifest digest");
  check(/faf558ec522716eb1b0979289f73782140a1812d73b2ae596040498f1dd74675/.test(detail.digests || ""), "the ELF digest");
  check(/LPS/.test(detail.machine || "") && /seqPolicy/.test(detail["clone policy"] || ""), "machine and clone policy");
  check(detail["proved run"] === "exit 0", `the proved run (${detail["proved run"]})`);
  check(/docker-test\.sh/.test(detail["try it"] || ""), "the command");
  const ths = await p.evaluate(() => [...document.querySelectorAll("#container-theorems code")].map((c) => c.textContent));
  check(ths.includes("Silmaril.Containers.Noop.wp_image"), "the theorem is listed");
  check(await p.evaluate(() => /answer THM/.test(document.body.textContent)), "the registry's answer");
  check(await p.evaluate(() => document.querySelector("#container-verdict [data-verdict]")?.textContent === "Proved"), "the page says Proved");
  await shot("container-noop");

  await open("/container/containers.http_serve.oci_wlp");
  const serve = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("#container-detail tr")]
    .map((tr) => [tr.cells[0].textContent.trim(), tr.cells[1].textContent.trim()])));
  check(/sha256:3f770ab28a5571ae2698a9e30cac5af8ecd4b2b8aa466c06a5872e1ef82b121a/.test(serve.digests || ""), "http-serve: the manifest digest");
  check(/1515fe739d0dbffcf92a6701d8a1b107df5f1c9a19dcf95400d3d904cd002f02/.test(serve.digests || ""), "http-serve: the ELF digest");
  check(/http_serve\.s/.test(serve.source || ""), "http-serve: the source");
  check(/http-serve\/docker-test\.sh/.test(serve["try it"] || ""), "http-serve: the command");
  check(/8080/.test(serve.runtime || "") && /seqPolicy/.test(serve["clone policy"] || ""), "http-serve: runtime and clone policy");
  const sths = await p.evaluate(() => [...document.querySelectorAll("#container-theorems code")].map((c) => c.textContent));
  check(sths.includes("Silmaril.Containers.HttpServe.servesImage"), "http-serve: the theorem is listed");
  check(await p.evaluate(() => document.querySelector("#container-verdict [data-verdict]")?.textContent === "Proved"), "http-serve: the page says Proved");
  await shot("container-http-serve");

  await open("/container/containers.examples.http");
  const http = await p.evaluate(() => Object.fromEntries([...document.querySelectorAll("#container-detail tr")]
    .map((tr) => [tr.cells[0].textContent.trim(), tr.cells[1].textContent.trim()])));
  check(/send "HTTP\/1\.1 200 OK"/.test(http["run computed now"] || ""), "the HTTP run computed now sends the 200 response");
  check(http.profile === "tcpOnly", "HTTP is TCP only");
  await shot("container-http");

  check(errors.length === 0, `no page errors (${errors.join("; ")})`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("all passed");
