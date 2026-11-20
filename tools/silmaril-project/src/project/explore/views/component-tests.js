// Component tests (#/component-tests): the component binaries of examples/component-tests, what
// is expected of their instantiation, the rows of the component test shapes that state it, how
// strong the theorems are, under which assumptions, and what the pinned wasmtime observed.
// Data: component-tests/report.json and component-tests/oracle.json next to the page (copied by
// `make pages`), with the .wasm and .wat files. `ComponentTests.render` is pure (no DOM, no
// database) and loads in Node's tests; the page adds the rows' status badges.
const ComponentTests = (() => {
  const e = (s) => String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const plink = (n) => `<a href="#/problem/${encodeURIComponent(n)}">${e(n)}</a>`;
  const list = (xs) => (xs && xs.length ? "<ul>" + xs.map((x) => `<li>${e(x)}</li>`).join("") + "</ul>" : '<span class="muted">(none)</span>');

  // The oracle's verdict on one binary: what wasmtime observed and whether it is what is expected.
  function oracleCell(o) {
    if (!o) return '<span class="muted">not run</span>';
    const obs = Object.entries(o.observed || {}).map(([k, v]) => `${e(k)}: <code>${e(JSON.stringify(v))}</code>`).join("<br>");
    const verdict = o.agrees ? '<span class="st st-ok" title="the observations are the expected ones">agrees</span>'
      : '<span class="st st-bad" title="the observations differ from the expected ones">DIFFERS</span>';
    return `${verdict}<br>${obs}<br><span class="muted">binary SHA-256 ${e((o.sha256 || "").slice(0, 16))}…` +
      `${o.embedded_verbatim ? ", embedded verbatim in the composition" : ""}</span>`;
  }

  // `report`, `oracle`: the two JSON files; `opts.badge(name)`: HTML of a row's status (optional);
  // `opts.base`: the directory of the files, relative to the page.
  function render(report, oracle, opts) {
    const o = opts || {}, badge = o.badge || (() => ""), base = o.base || "component-tests/";
    const ob = (oracle && oracle.binaries) || {};
    let h = "<h2>Component tests</h2><p>Component binaries whose behaviour at <b>instantiation</b> is stated by rows of the " +
      "component test shapes and proved in Lean; the pinned wasmtime is run on the same bytes as an independent oracle (not a proof).</p>";
    h += `<p><b>Semantics.</b> ${e(report.semantics)}</p>`;
    h += "<p><b>Assumptions.</b></p>" + list(report.assumptions);
    h += "<p><b>Shapes.</b> " + (report.shapes || []).map((s) => `${plink(s.name)} ${badge(s.name)} <code>${e(s.lean)}</code>`).join("; ") + "</p>";
    for (const b of report.binaries || []) {
      const x = ob[b.name];
      if (x && x.sha256 !== b.sha256) h += `<p class="err">${e(b.name)}: the oracle ran on other bytes (${e(x.sha256)})</p>`;
      h += `<h3><code>${e(b.wasm)}</code></h3><div class="tablebox"><table><tbody>`;
      const row = (k, v) => { h += `<tr><th style="text-align:left;vertical-align:top">${e(k)}</th><td>${v}</td></tr>`; };
      row("binary", `<a href="${e(base + b.wasm)}" download>${e(b.wasm)}</a> (${e(b.size)} B, SHA-256 <code>${e(b.sha256)}</code>) · ` +
        `<a href="${e(base + b.wat)}" target="_blank">${e(b.wat)}</a> · Lean <code>${e(b.lean)}</code>`);
      row("imports", list(b.imports));
      row("exports", list(b.exports));
      row("core instances, in order", list(b.core_instances));
      const ex = b.expected || {};
      row("expected", `instantiation: <b>${e(ex.instantiation)}</b>; import trace: ${ex.trace && ex.trace.length ? ex.trace.map((t) => `<code>${e(t)}</code>`).join(", ") : "none"}` +
        (ex.exports && ex.exports.length ? "; then " + ex.exports.map(([q, v]) => `<code>${e(q)}</code> = <code>${e(v)}</code>`).join(", ") : ""));
      row("rows", (b.rows || []).map((r) => `${plink(r.name)} ${badge(r.name)} <span class="muted">(${e(r.shape)}; <code>${e(r.theorem)}</code>)</span>`).join("<br>"));
      row("theorem strength", e(b.strength));
      if (b.ref) row("reference machine", `<code>${e(b.ref.theorem)}</code>: ${e(b.ref.strength)}`);
      if (b.bridge) row("decoder bridge: core instantiations", `<code>${e(b.bridge.theorem)}</code>: ${e(b.bridge.strength)}`);
      if (b.bridge_wiring) row("decoder bridge: wiring and types (fragment)", `<code>${e(b.bridge_wiring.theorem)}</code>: ${e(b.bridge_wiring.strength)}`);
      if (b.bridge_semantic) row("IR vs REF behaviour", e(b.bridge_semantic));
      row("oracle (wasmtime)", oracleCell(x));
      h += "</tbody></table></div>";
    }
    if ((report.regressions || []).length) {
      h += "<h3>Decoder bridge regressions</h3><p>Binaries on which the two readings (IR: <code>Binary.parseComponent</code>; " +
        "REF: <code>Conformance.decodeRef</code>) are shown to disagree, from kernel runs; no rows, no oracle run.</p>";
      for (const g of report.regressions) {
        h += `<h4><code>${e(g.wasm)}</code></h4><div class="tablebox"><table><tbody>`;
        const row = (k, v) => { h += `<tr><th style="text-align:left;vertical-align:top">${e(k)}</th><td>${v}</td></tr>`; };
        row("binary", `<a href="${e(base + g.wasm)}" download>${e(g.wasm)}</a> (${e(g.size)} B, SHA-256 <code>${e(g.sha256)}</code>) · ` +
          `<a href="${e(base + g.wat)}" target="_blank">${e(g.wat)}</a> · Lean <code>${e(g.lean)}</code>`);
        row("content", e(g.what));
        row("facts", (g.facts || []).map((f) => `<code>${e(f.theorem)}</code>: ${e(f.statement)}`).join("<br>"));
        row("status", e(g.status));
        if (g.cause) row("cause", e(g.cause));
        if (g.resolution) row("resolution", e(g.resolution));
        h += "</tbody></table></div>";
      }
    }
    if (oracle && oracle.tools) {
      h += "<p><b>Oracle provenance.</b> " + Object.entries(oracle.tools).map(([k, t]) =>
        `${e(k)} ${e(t.version)} (SHA-256 <code>${e(t.sha256)}</code>)`).join("; ") + `. ${e(oracle.note || "")}</p>`;
    }
    return h;
  }
  return { render };
})();

if (typeof registerView === "function") {
  registerView({
    id: "component-tests", title: "Component tests", nav: 73, render: async () => {
      const get = async (f) => { const r = await fetch("component-tests/" + f); if (!r.ok) throw new Error(`component-tests/${f}: HTTP ${r.status}`); return r.json(); };
      let report, oracle = null;
      try { report = await get("report.json"); } catch (err) {
        return `<p class="err">The component-test data is not available here (${esc(err.message || err)}). ` +
          "<code>make pages</code> copies <code>examples/component-tests</code> next to the page.</p>";
      }
      try { oracle = await get("oracle.json"); } catch (err) { oracle = null; }
      return ComponentTests.render(report, oracle, { badge: (n) => statusBadge(n) });
    },
  });
}
if (typeof module !== "undefined" && module.exports) module.exports = ComponentTests;
