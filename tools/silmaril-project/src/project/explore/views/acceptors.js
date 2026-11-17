// ---------- acceptor components: runtime observations and Lean theorems ----------
// A section on the pages of a Wasm component and of a registry artifact whose SHA-256 is that of a
// certificate-checking acceptor component. Two kinds of evidence, kept apart on the page:
// * runtime observations: `acceptor-runs.json` next to the page, the report of
//   tools/wasm-acceptor-harness (kind `silmaril.wasm-acceptor-harness.report/v2`, or v1, which
//   has no claims), copied by `make pages`. Each case is one call of one export under one engine
//   on concrete arguments. An observation is a test, never a proof: it gets neutral badges only,
//   a met expectation reads "matches expectation (test)", a missing one is neutral. The verdict
//   is recomputed here from the expected outcome (and expected detail substring) and the
//   observation; a report whose own verdict disagrees is flagged.
// * Lean theorems: the `claims` of the report's artifacts (v2), which the harness copies from the
//   suite files (tools/wasm-acceptor-harness/suites/*.json) only when the file has the pinned
//   SHA-256, each with the SHA-256 it was made for. A claim shows only on a page whose SHA-256 is
//   both the artifact's and the claim's. Nothing here checks them: the names are what the library
//   states (CI builds it with --wfail), linked to their source when the page has sources.
// Missing report: a neutral notice on component pages (and so no claims). A malformed report: an
// error in this section's block. Adding a checker is adding a suite file: there is no per-checker code here.
(() => {
  const { esc, href } = Explorer.ui;
  const REPORT = "acceptor-runs.json";
  const KINDS = ["silmaril.wasm-acceptor-harness.report/v2", "silmaril.wasm-acceptor-harness.report/v1"];
  let reportP = null;
  // The report, or { missing: reason } when there is none next to the page. Anything else that
  // goes wrong (not JSON, another kind) is an error.
  async function loadReport() {
    if (!reportP) reportP = (async () => {
      let r;
      try { r = await fetch(REPORT, { cache: "no-cache" }); }
      catch (e) { return { missing: `${REPORT} could not be fetched here (${e.message || e})` }; }
      if (r.status === 404) return { missing: `there is no ${REPORT} next to this page` };
      if (!r.ok) throw new Error(`${REPORT}: HTTP ${r.status}`);
      let j;
      try { j = await r.json(); } catch (e) { throw new Error(`${REPORT} is not JSON (${e.message || e})`); }
      if (!j || !KINDS.includes(j.kind)) throw new Error(`${REPORT}: kind ${JSON.stringify(j && j.kind)}, expected one of ${KINDS.join(", ")}`);
      if (!j.engine || !Array.isArray(j.artifacts) || !Array.isArray(j.cases)) throw new Error(`${REPORT}: no engine, artifacts or cases`);
      return j;
    })();
    try { return await reportP; } catch (e) { reportP = null; throw e; }
  }

  const code = (s) => `<code>${esc(s)}</code>`;
  const obsTag = (cls, text, title) => `<span class="obs${cls ? " obs-" + cls : ""}" title="${esc(title)}">${esc(text)}</span>`;
  // An argument, abbreviated: `{"$repeat": v, "count": n}` as `[v × n]`, long JSON cut.
  function brief(a) {
    if (a && typeof a === "object" && !Array.isArray(a) && "$repeat" in a) return `[${brief(a.$repeat)} × ${a.count}]`;
    const s = JSON.stringify(a);
    return s.length > 48 ? s.slice(0, 45) + "…" : s;
  }
  function argsCell(c) {
    const full = JSON.stringify(c.args);
    const t = full.length > 2000 ? full.slice(0, 2000) + "…" : full;
    return `<code title="${esc(t)}">${esc((c.args || []).map(brief).join(", "))}</code>`;
  }
  // The verdict from the expectation and the observation (the report's own is only compared):
  // the outcome must be the expected one and, when an expected detail is given, the observed
  // detail must contain it.
  function verdict(c) {
    const obs = c.observed && c.observed.outcome, detail = (c.observed && c.observed.detail) || "";
    const want = c.expected_detail;
    const detailOk = want == null || detail.includes(want);
    const mine = c.expected == null ? "unchecked" : c.expected === obs && detailOk ? "pass" : "fail";
    let h = mine === "pass" ? obsTag("match", "matches expectation (test)", `this run's outcome ${obs} is the expected one; a test, not a proof`)
      : mine === "fail" && c.expected === obs ? obsTag("mismatch", `mismatch: detail lacks ${JSON.stringify(want)}`, `expected a detail containing ${JSON.stringify(want)}, observed ${JSON.stringify(detail)}`)
      : mine === "fail" ? obsTag("mismatch", `mismatch: expected ${c.expected}`, `expected ${c.expected}, observed ${obs}`)
      : obsTag("", "no expectation", "the case states no expected outcome: nothing is checked");
    if (c.verdict !== mine) h += ` <span class="st-x st-x-bad" title="the report's verdict is not what its expected and observed outcomes give">report says ${esc(c.verdict)}</span>`;
    return { mine, html: h };
  }
  function observationsBlock(rep, art, subject) {
    const eng = rep.engine || {};
    const engName = String(eng.name || "engine").replace(/^./, (x) => x.toUpperCase());
    const cases = rep.cases.filter((c) => c.sha256 === art.sha256);
    const vs = cases.map(verdict), n = (k) => vs.filter((v) => v.mine === k).length;
    let h = `<h3>Runtime observations (${esc(engName)} ${esc(eng.version || "?")}) — tested, not proved</h3>`;
    h += `<p class="muted">The report: “${esc(rep.evidence || "runtime observations; not a proof")}”. Each case calls one export of these exact bytes, ` +
      "in a fresh store and instance, on concrete arguments; an outcome is what this engine build did, not a property of every run " +
      "or every engine. The report is regenerated in CI and must equal the committed one.</p>";
    const cidOk = !subject.cid || subject.cid === art.cid;
    const rows = [["artifact", code(art.id) + (art.source ? ` <span class="muted">${esc(art.source)}</span>` : "")],
      ["SHA-256", code(art.sha256) + ' <span class="muted">= this page\'s</span>'],
      ["CID (BLAKE3)", code(art.cid) + (subject.cid ? (cidOk ? ' <span class="muted">= this page\'s</span>'
        : ` <span class="st-x st-x-bad">≠ this page's ${esc(subject.cid)}</span>`) : "")],
      ["bytes", esc(art.bytes) + " B" + (art.pinned_sha256_ok === false ? ' <span class="st-x st-x-bad">pinned SHA-256 mismatch</span>' : "")],
      ["engine", code(`${eng.name} ${eng.version}`)],
      ["config", Object.entries(eng.config || {}).map(([k, v]) => `${esc(k)}: ${code(typeof v === "string" ? v : JSON.stringify(v))}`).join("<br>")],
      ["command", code((rep.command || []).join(" "))],
      ["cases", `${cases.length}: ${n("pass")} match their expectation, ${n("fail")} mismatch, ${n("unchecked")} without expectation`]];
    h += '<dl class="obs-meta">' + rows.map(([k, v]) => `<dt>${esc(k)}</dt><dd>${v}</dd>`).join("") + "</dl>";
    if (!cases.length) return h + '<p class="muted">The report lists these bytes but no case runs them.</p>';
    const cols = [["case", (c) => code(c.name) + (c.note ? `<div class="muted">${esc(c.note)}</div>` : "")],
      ["export", (c) => code(`${c.export}(${(c.params || []).join(", ")})`)],
      ["class", (c) => esc(c.class || "")],
      ["args", argsCell],
      ["expected", (c) => c.expected == null ? '<span class="muted">none</span>' : code(c.expected) +
        (c.expected_detail != null ? `<div class="muted">detail contains ${code(c.expected_detail)}</div>` : "")],
      ["observed", (c) => code(c.observed.outcome) + (c.observed.detail ? `<div class="muted">${esc(c.observed.detail)}</div>` : "")],
      ["verdict", (c, i) => vs[i].html]];
    return h + '<div class="tablebox"><table class="obs-cases"><thead><tr>' + cols.map(([t]) => `<th>${esc(t)}</th>`).join("") +
      "</tr></thead><tbody>" + cases.map((c, i) => `<tr data-case="${esc(c.name)}" data-verdict="${vs[i].mine}">` +
        cols.map(([, f]) => `<td>${f(c, i)}</td>`).join("") + "</tr>").join("") + "</tbody></table></div>";
  }
  // The claims of the report about exactly these bytes: those of an artifact with this SHA-256
  // whose own SHA-256 (the pin it was made for) is this one too. Duplicates (one artifact in two
  // suites) are shown once.
  function claimsFor(rep, sha) {
    const seen = new Set(), out = [];
    for (const a of rep.artifacts) {
      if (a.sha256 !== sha || a.pinned_sha256_ok === false) continue;
      for (const cl of Array.isArray(a.claims) ? a.claims : []) {
        if (!cl || cl.sha256 !== sha) continue;
        const key = JSON.stringify(cl);
        if (!seen.has(key)) { seen.add(key); out.push(Object.assign({ artifact: a.id }, cl)); }
      }
    }
    return out;
  }
  const LEVEL_CLASS = { component: "prov prov-lean", "core-module": "prov prov-browser" };
  // The source of a claimed theorem. A module the page's source map knows keeps its usual links
  // (file, view, the declaration's own page). A library module it does not know (the database
  // lists only the modules of its own problems) links to its file at the page's pinned revision:
  // `Silmaril.A.B` is `Silmaril/A/B.lean` and `ProjectSelfTest.A` is
  // `examples/project/ProjectSelfTest/A.lean` by the library layout (lakefile.toml); only names
  // of those shapes are mapped. Without a pinned revision nothing is linked, and the page says so.
  // library roots (lakefile.toml): `Silmaril.*` under the repository root, the self-test library
  // `ProjectSelfTest.*` under examples/project/
  const LIB_ROOTS = [[/^Silmaril(\.[A-Za-z][A-Za-z0-9_]*)+$/, ""], [/^ProjectSelfTest(\.[A-Za-z][A-Za-z0-9_]*)+$/, "examples/project/"]];
  function claimSource(t, knownDecl) {
    // the source map knows the module: its file (and, when the database knows the declaration,
    // the view button and the declaration's own page)
    const known = sourceLink(t.module, knownDecl ? t.decl : null);
    if (known) return known;
    const root = typeof t.module === "string" ? LIB_ROOTS.find(([re]) => re.test(t.module)) : null;
    if (!root) return '<span class="muted">—</span>';
    const f = repoFile(root[1] + t.module.replace(/\./g, "/") + ".lean");
    if (!f) return '<span class="muted" data-claim-source="none">no pinned source revision on this page</span>';
    return `<a class="claim-src" href="${esc(f.blob)}" target="_blank" rel="noopener noreferrer" title="${esc(f.path)} at ${esc(SOURCE.rev.slice(0, 12))}">source</a>`;
  }
  function claimBlock(cl, known) {
    const cls = LEVEL_CLASS[cl.level] || "prov";
    let h = `<p><span class="${cls}" data-claim="${esc(cl.level || "")}">${esc(cl.kind || "claim")}</span> ` +
      `<span class="muted">${esc(cl.scope || "")}</span></p>`;
    const rows = [["about", code(cl.value || "?") + (cl.registry_name ? ` <span class="muted">registered as</span> ${code(cl.registry_name)}` : "")],
      ["for SHA-256", code(cl.sha256) + ' <span class="muted">= this page\'s</span>'],
      ["stated in", `the suite of ${code(cl.artifact)} (<code>tools/wasm-acceptor-harness/suites/</code>), copied into the report`]];
    h += '<dl class="obs-meta">' + rows.map(([k, v]) => `<dt>${esc(k)}</dt><dd>${v}</dd>`).join("") + "</dl>";
    const ths = Array.isArray(cl.theorems) ? cl.theorems : [];
    h += '<div class="tablebox"><table class="claims"><thead><tr><th>theorem</th><th>states</th><th>source</th></tr></thead><tbody>' +
      ths.map((t) => `<tr><td>${known.has(t.decl) ? `<a href="${esc(href("source", t.decl))}">${code(t.decl)}</a>` : code(t.decl)}` +
        `<div class="muted">${esc(t.module)}</div></td><td>${esc(t.states)}</td><td>${claimSource(t, known.has(t.decl))}</td></tr>`).join("") +
      "</tbody></table></div>";
    return h;
  }
  // The claimed declarations the database knows (as #/source does: a location, a problem's or an
  // answer's declaration); only these get a link to their own page.
  async function knownDecls(rep, sha, ctx) {
    const decls = [...new Set(claimsFor(rep, sha).flatMap((c) => (Array.isArray(c.theorems) ? c.theorems : []).map((t) => t.decl)))];
    const known = new Set();
    if (!ctx || !decls.length) return known;
    for (const d of decls) {
      const hit = (await ctx.tq("decl_locations", "SELECT 1 AS x FROM decl_locations WHERE decl = ?", [d])).length ||
        (await ctx.q("SELECT 1 AS x FROM problems WHERE decl = ? LIMIT 1", [d])).length ||
        (await ctx.q("SELECT 1 AS x FROM answers WHERE decl = ? LIMIT 1", [d])).length;
      if (hit) known.add(d);
    }
    return known;
  }
  function claimsBlock(rep, sha, known) {
    const withheld = rep.artifacts.filter((a) => a.sha256 === sha && a.claims_withheld).map((a) => a.claims_withheld);
    const note = withheld.map((w) => `<p class="muted"><span class="st-x st-x-bad">${esc(w)}</span></p>`).join("");
    if (!String(rep.kind).endsWith("/v2"))
      return note + `<p class="muted claims-none">No Lean theorem about these bytes is named: this report (${esc(rep.kind)}) carries no claims.</p>`;
    const cls = claimsFor(rep, sha);
    if (!cls.length) return note + '<p class="muted claims-none">No Lean theorem about these bytes is named in the report.</p>';
    let h = "<h3>Lean theorems about this component</h3>";
    h += '<p class="muted">Read from the harness report, which copies them from the suite file for exactly these bytes (the pinned SHA-256); ' +
      "not read from the database and not checked by the harness or here. Separate from the runtime observations, which they neither use nor confirm.</p>";
    return h + note + cls.map((cl) => claimBlock(cl, known)).join("");
  }
  async function render(subject, ctx) {
    const sha = (subject.sha256 || "").toLowerCase();
    if (!/^[0-9a-f]{64}$/.test(sha)) return "";
    const rep = await loadReport();
    // Without a report nothing here names these bytes: a neutral notice on component pages (any
    // component may be an acceptor), nothing on artifact pages.
    if (rep.missing) return subject.kind !== "wasm-component" ? "" :
      `<p class="muted obs-none">No runtime observations or claims: ${esc(rep.missing)}. Both come from the report of ` +
      "<code>tools/wasm-acceptor-harness</code> (<code>report.json</code>, copied by <code>make pages</code>).</p>";
    const art = rep.artifacts.find((a) => a.sha256 === sha);
    if (!art) return "";
    return observationsBlock(rep, art, subject) + claimsBlock(rep, sha, await knownDecls(rep, sha, ctx));
  }
  Explorer.registerSection({ id: "acceptor-evidence", title: "Acceptor component: runtime observations and theorems",
    on: ["wasm-component", "artifact"], order: 40, render });
})();
