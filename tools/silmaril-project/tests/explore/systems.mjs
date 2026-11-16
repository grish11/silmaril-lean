// The Systems view (docs/projects/consequence-systems.md), in Chromium, on a site built from the
// self-test database (`make project-check`, then `sil project explore`, or `make pages`):
// * #/systems lists the self-test's consequence systems with their constructions, and the table
//   of what each status of each standard shape means;
// * a system's page shows its definition, construction (operands, witness system) and every
//   standard problem that names it, as S or as T, with the outcome, the reading for the arguments
//   left free and the Lean answers with their witnesses (the counterexample ff ⊢ p is kept);
// * a closed refutation is stored UNS and reads false, an expected negative result is a match, and
//   universality, context-universality and deriving ff are named apart;
// * no page error, and a database without the tables gets a notice.
//   node systems.mjs SITE_DIR [SHOTS_DIR]
import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
const pw = await import(process.env.PLAYWRIGHT_CORE || "/usr/local/lib/node_modules/playwright-core/index.mjs");
const site = path.resolve(process.argv[2]), shots = process.argv[3] && path.resolve(process.argv[3]);
const port = 8799;
const srv = spawn("python3", ["-I", path.join(path.dirname(new URL(import.meta.url).pathname), "pages_server.py"),
  "--root", site, "--port", String(port), "--log", path.join(os.tmpdir(), "systems_requests.jsonl")], { stdio: "ignore" });
const fails = [];
const check = (ok, what) => { console.log((ok ? "ok   " : "FAIL ") + what); if (!ok) fails.push(what); };
const S = "silmaril.selftest.consequence.";
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
  // each row: its cells' text, the first cell being the text of its first link (the name)
  const rows = (sel) => p.evaluate((sel) => [...document.querySelectorAll(sel + " tbody tr")].map((tr) =>
    [...tr.children].map((td, i) => (i === 0 && td.querySelector("a") ? td.querySelector("a") : td).textContent.trim())), sel);

  // the list
  await open("/systems");
  const nav = await p.evaluate(() => [...document.querySelectorAll("#nav a")].map((a) => a.getAttribute("href")));
  check(nav.includes("#/systems"), "Systems is in the navigation");
  const list = await rows("#systems-table");
  const byName = Object.fromEntries(list.map((r) => [r[0], r]));
  for (const n of ["raw", "hyp", "raw_or_hyp", "derivable", "entails", "gap", "checked", "empty"]) check(byName[S + n], `listed: ${n}`);
  check(/erase of the witness system ProjectSelfTest\.Consequence\.Deriv/.test(byName[S + "derivable"][2]), "derivable is the erasure of Deriv");
  check(/^union of .*raw, .*hyp$/.test(byName[S + "raw_or_hyp"][2]) && /^diff of .*entails, .*derivable$/.test(byName[S + "gap"][2]),
    "constructions name their operands in order");
  check(/List ProjectSelfTest\.Consequence\.Atom → ProjectSelfTest\.Consequence\.Atom/.test(byName[S + "raw"][3]), "contexts → conclusions");
  const qs = await rows("#systems-questions");
  check(qs.length === 7 && qs[0][2].includes("universal") && qs[0][4].includes("empty"), "the questions table: derives THM universal, UNS empty");
  check(qs.find((r) => r[0] === "derives_bottom")[4].includes("no context derives ff"), "derives_bottom UNS: no context derives ff");
  await shot("systems");

  // a system: derivable
  await open("/system/" + encodeURIComponent(S + "derivable"));
  const dl = await p.evaluate(() => document.querySelector("#main dl").textContent);
  check(/erasure of a witness system/.test(dl) && /ProjectSelfTest\.Consequence\.Deriv/.test(dl) && /used by/.test(dl), "definition, construction, witness system, used by");
  const ps = await rows("#system-problems");
  const by = Object.fromEntries(ps.map((r) => [r[0], r]));
  const row = (n) => by[S + n] || [];
  check(/THM/.test(row("p_derives_r")[4]) && /holds in/.test(row("p_derives_r")[5]), "p ⊢ r: THM, holds");
  const rp = await p.evaluate((n) => { const a = [...document.querySelectorAll("#system-problems a")].find((x) => x.textContent === n);
    const st = a.closest("tr").querySelector(".st"); return { code: st.dataset.code, outcome: st.dataset.outcome, title: st.title }; }, S + "r_derives_p");
  check(rp.code === "UNS" && rp.outcome === "match" && /closed proposition: false/.test(rp.title) && /does not hold/.test(row("r_derives_p")[5]),
    `r ⊢ p: a closed refutation, stored UNS, expected, false, does not hold (${JSON.stringify(rp)})`);
  check(/sound for/.test(row("derivable_sound")[5]) && /T = .*entails/.test(row("derivable_sound")[3]), "soundness for entails");
  check(/CSA/.test(row("derivable_complete")[4]) && /✓/.test(row("derivable_complete")[4]) && /not complete/.test(row("derivable_complete")[5]) &&
    /Atom\.ff\]/.test(row("derivable_complete")[6]) && /Atom\.p/.test(row("derivable_complete")[6]), "incompleteness with the counterexample ff ⊢ p");
  check(/NOC/.test(row("derivable_universal")[4]) && /derives something, and is not universal/.test(row("derivable_universal")[5]),
    "derives: contingent is NOC, read as nonempty and not universal");
  check(/does not derive every conclusion/.test(row("derivable_ff_universal")[5]), "context_universal at ff: CSA, named context-universal");
  check(/some contexts derive .*ff/.test(row("derivable_derives_ff")[5]), "derives_bottom: contingent, named derives ff");
  check(/preserves/.test(row("shift_preserves")[5]) && /does not reflect/.test(row("shift_reflects")[5]), "translation preserves, does not reflect");
  check(!ps.some((r) => /\binconsistent\b/i.test(r[5])), "no reading says an unqualified 'inconsistent'");
  await shot("system-derivable");

  // entails: the same problems from the other side, and context-universality
  await open("/system/" + encodeURIComponent(S + "entails"));
  const es = await rows("#system-problems");
  check(es.some((r) => r[0] === S + "derivable_sound" && r[2] === "T"), "entails appears as T of soundness");
  check(es.some((r) => r[0] === S + "entails_ff_universal" && /context-universal/.test(r[5])), "entails: ff is context-universal");
  await shot("system-entails");

  // the empty system and an unknown name
  await open("/system/" + encodeURIComponent(S + "empty"));
  check((await rows("#system-problems")).some((r) => /UNS/.test(r[4]) && /empty: it derives nothing/.test(r[5])), "the empty system: UNS, derives nothing");
  await open("/system/no.such.system");
  check(await p.evaluate(() => /no consequence system/.test(document.querySelector("#main").textContent)), "an unknown system is reported");

  check(errors.length === 0, `no page error${errors.length ? ": " + errors.join("; ") : ""}`);
} finally {
  await b.close();
  srv.kill();
}
if (fails.length) { console.log(`${fails.length} failed`); process.exit(1); }
console.log("systems: ok");
