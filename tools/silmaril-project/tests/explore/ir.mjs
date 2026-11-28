// Opt-in browser check against the project's real export from make project-check or make pages.
// node ir.mjs EXPLORER_URL [SCREENSHOT.png]
import assert from "node:assert/strict";
import fs from "node:fs";

const [address, screenshot] = process.argv.slice(2);
assert(address, "usage: node ir.mjs EXPLORER_URL [SCREENSHOT.png]");
const url = new URL(address);
url.hash = "/ir/";
const { chromium } = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const bundledChrome = "/opt/ms-playwright/chromium-1248/chrome-linux64/chrome";
const browser = await chromium.launch({
  executablePath: process.env.CHROME || (fs.existsSync(bundledChrome) ? bundledChrome : undefined),
});
try {
  const page = await browser.newPage({ viewport: { width: 1500, height: 1050 } });
  const errors = [];
  page.on("pageerror", (error) => errors.push(error.message));
  const settle = (view) => page.waitForFunction((id) =>
    window.explore?.ready && !window.explore.busy && window.explore.view === id, view);
  await page.goto(url.href);
  await settle("ir");

  const table = page.locator("#ir-registry");
  const cf = table.locator("tbody tr").filter({ has: page.getByText("mlir.cf", { exact: true }) });
  assert.equal(await cf.count(), 3);
  const expected = [
    ["mlir.cf.basic_scalar_loop", "mlir.cf.basic_scalar_loop_part", "denotational"],
    ["mlir.cf.switch_assert", "mlir.cf.switch_assert_part", "denotational"],
    ["mlir.cf.switch_assert", "mlir.cf.switch_assert_run", "operational"],
  ];
  for (const [subset, model, reading] of expected) {
    const row = cf.filter({ has: page.getByText(model, { exact: true }) });
    assert.equal(await row.count(), 1, model);
    assert.equal(await row.getByText(subset, { exact: true }).count(), 1, model);
    assert.equal(await row.getByText("Typed SSA control-flow graphs", { exact: true }).count(), 1, model);
    assert.equal(await row.getByText(reading, { exact: true }).count(), 1, model);
  }
  if (screenshot) await page.screenshot({ path: screenshot, fullPage: true });

  const basic = cf.filter({ has: page.getByText("mlir.cf.basic_scalar_loop_part", { exact: true }) });
  const observe = "Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.observe";
  await basic.getByRole("link", { name: observe, exact: true }).click();
  await settle("source");
  assert((await page.locator("main h2").innerText()).includes(observe));

  await page.goto(url.href);
  await settle("ir");
  const institution = basic.locator('a[href="#/institution/ssa.mlir.cf.scalar_loop"]');
  await institution.click();
  await settle("institution");
  assert((await page.locator("main").innerText()).includes(
    "Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Institution.targetInst"));
  assert.deepEqual(errors, []);
  console.log("CF registry rows, model source, and scalar-loop institution passed");
} finally {
  await browser.close();
}
