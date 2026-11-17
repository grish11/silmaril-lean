// ---------- acceptor components: runtime observations and Lean theorems ----------
// A section on the pages of a Wasm component and of a registry artifact whose SHA-256 is that of a
// certificate-checking acceptor component. Two kinds of evidence, kept apart on the page:
// * runtime observations: `acceptor-runs.json` next to the page, the report of
//   tools/wasm-acceptor-harness (kind `silmaril.wasm-acceptor-harness.report/v1`), copied by
//   `make pages`. Each case is one call of one export under one engine on concrete arguments.
//   An observation is a test, never a proof: it gets neutral badges only, a met expectation reads
//   "matches expectation (test)", a missing one is neutral. The verdict is recomputed here from
//   the expected and observed outcomes; a report whose own verdict disagrees is flagged.
// * Lean theorems: `CLAIMS`, a static map by SHA-256 from the bytes a theorem is about to the
//   theorem names and the kind of claim. Nothing here checks them: the names are what the library
//   states (CI builds it with --wfail), linked to their source when the page has sources.
// Missing report: a neutral notice. A malformed report: an error in this section's block.
(() => {
  const { esc, href } = Explorer.ui;
  const REPORT = "acceptor-runs.json";
  const KIND = "silmaril.wasm-acceptor-harness.report/v1";
  // By the SHA-256 of the bytes the theorems are about (the file the harness pins). A changed
  // file no longer matches, so a claim never shows on bytes it was not made for.
  const CLAIMS = [
    { sha256: "a9570103fe3a7074b0d354aebf03538e1f5b78a90fe4c4631980866dc7e2ace2", name: "silmaril.wasm.examples.sat_accept.component",
      kind: "component-level soundness (kernel-checked)", level: "component",
      scope: "Every reference Component Model reading of what the bytes parse to (Silmaril.Wasm.Examples.SatAccept.bytes, " +
        "regenerated as examples/wasm-acceptors/sat_accept.wasm): an accepting call implies the SAT check and language " +
        "membership. Soundness only: nothing is stated about rejections, traps or completeness.",
      theorems: [
        { decl: "Silmaril.Project.WasmComponents.SatAccept.checkStream_sound_of_bytes", module: "Silmaril.Project.WasmComponents.SatAccept.Thms",
          states: "check-stream returns true on xs, ms ⇒ satStream xs ms = true ∧ xs ∈ SatStream" },
        { decl: "Silmaril.Project.WasmComponents.SatAccept.checkNested_sound_of_bytes", module: "Silmaril.Project.WasmComponents.SatAccept.Thms",
          states: "check-nested returns true on p, ms ⇒ satNested p ms = true ∧ p ∈ SatNested" }] },
    { sha256: "d761553e57d20813207aa1df1e19168787ec8e7dd8fcef253dc4f4369221a784", name: "silmaril.wasm.examples.lrat_accept.component",
      kind: "component-level soundness (kernel-checked)", level: "component",
      scope: "Every reference Component Model reading of what the bytes parse to (Silmaril.Wasm.Examples.LratAccept.bytes, " +
        "regenerated as examples/wasm-acceptors/lrat_accept.wasm): an accepting call implies that the problem is unsatisfiable. " +
        "Soundness only: nothing is stated about rejections, traps or completeness (the checker is bounded).",
      theorems: [
        { decl: "Silmaril.Project.WasmComponents.LratAccept.checkStream_sound_of_bytes", module: "Silmaril.Project.WasmComponents.LratAccept.Thms",
          states: "check-stream returns true on xs, cert ⇒ xs ∈ UnsatStream" },
        { decl: "Silmaril.Project.WasmComponents.LratAccept.checkNested_sound_of_bytes", module: "Silmaril.Project.WasmComponents.LratAccept.Thms",
          states: "check-nested returns true on p, cert ⇒ p ∈ UnsatNested" }] },
    { sha256: "f3048c4e556e99ab1ad0c3f7a1f9528f4d1f5a25801b442587391f3f75bce996", name: "silmaril.wasm.examples.farkas_accept.component",
      kind: "core-module soundness only", level: "core",
      scope: "About the core module inside the component (Core 3.0 small-step execution), not about the component's " +
        "canonical ABI lift and lowering; component-level proofs are in progress.",
      theorems: [
        { decl: "Silmaril.Wasm.Examples.FarkasAccept.check_sound", module: "Silmaril.Wasm.Examples.FarkasAccept.Thms",
          states: "core check returning nonzero ⇒ the system read from memory is infeasible" }] }];

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
      if (!j || j.kind !== KIND) throw new Error(`${REPORT}: kind ${JSON.stringify(j && j.kind)}, expected ${KIND}`);
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
  // The verdict from the expectation and the observation (the report's own is only compared).
  function verdict(c) {
    const obs = c.observed && c.observed.outcome;
    const mine = c.expected == null ? "unchecked" : c.expected === obs ? "pass" : "fail";
    let h = mine === "pass" ? obsTag("match", "matches expectation (test)", `this run's outcome ${obs} is the expected one; a test, not a proof`)
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
      ["expected", (c) => c.expected == null ? '<span class="muted">none</span>' : code(c.expected)],
      ["observed", (c) => code(c.observed.outcome) + (c.observed.detail ? `<div class="muted">${esc(c.observed.detail)}</div>` : "")],
      ["verdict", (c, i) => vs[i].html]];
    return h + '<div class="tablebox"><table class="obs-cases"><thead><tr>' + cols.map(([t]) => `<th>${esc(t)}</th>`).join("") +
      "</tr></thead><tbody>" + cases.map((c, i) => `<tr data-case="${esc(c.name)}" data-verdict="${vs[i].mine}">` +
        cols.map(([, f]) => `<td>${f(c, i)}</td>`).join("") + "</tr>").join("") + "</tbody></table></div>";
  }
  function claimsBlock(cl) {
    const cls = cl.level === "component" ? "prov prov-lean" : "prov prov-browser";
    let h = `<h3>Lean theorems about this component</h3><p><span class="${cls}" data-claim="${esc(cl.level)}">${esc(cl.kind)}</span> ` +
      `<span class="muted">${esc(cl.scope)}</span></p>`;
    h += '<p class="muted">Named by a static map in the explorer (by SHA-256 of the bytes they are about), not read from the database; ' +
      "separate from the runtime observations, which they neither use nor confirm.</p>";
    h += '<div class="tablebox"><table class="claims"><thead><tr><th>theorem</th><th>states</th><th>source</th></tr></thead><tbody>' +
      cl.theorems.map((t) => `<tr><td><a href="${esc(href("source", t.decl))}">${code(t.decl)}</a><div class="muted">${esc(t.module)}</div></td>` +
        `<td>${esc(t.states)}</td><td>${sourceLink(t.module, t.decl) || '<span class="muted">—</span>'}</td></tr>`).join("") +
      "</tbody></table></div>";
    return h;
  }
  async function render(subject) {
    const sha = (subject.sha256 || "").toLowerCase();
    if (!/^[0-9a-f]{64}$/.test(sha)) return "";
    const cl = CLAIMS.find((c) => c.sha256 === sha);
    const rep = await loadReport();
    const art = rep.missing ? null : rep.artifacts.find((a) => a.sha256 === sha);
    if (!cl && !art) return "";
    let h = "";
    if (rep.missing) h += `<p class="muted obs-none">No runtime observations: ${esc(rep.missing)}. They are written by ` +
      "<code>tools/wasm-acceptor-harness</code> (<code>report.json</code>, copied by <code>make pages</code>).</p>";
    else if (art) h += observationsBlock(rep, art, subject);
    else h += '<p class="muted obs-none">No runtime observations: the harness report next to this page runs no artifact with this SHA-256.</p>';
    if (cl) h += claimsBlock(cl);
    else h += '<p class="muted">No Lean theorem about these bytes is named here.</p>';
    return h;
  }
  Explorer.registerSection({ id: "acceptor-evidence", title: "Acceptor component: runtime observations and theorems",
    on: ["wasm-component", "artifact"], order: 40, render });
})();
