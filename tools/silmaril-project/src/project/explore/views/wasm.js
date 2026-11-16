let wcy = null;
const disposeWcy = () => { if (wcy) { wcy.destroy(); wcy = null; } };
const wasmCache = new Map();
async function wasmJson(rel) {
  if (!wasmCache.has(rel)) wasmCache.set(rel, fetch("wasm/" + rel).then((r) => {
    if (!r.ok) throw new Error(`wasm/${rel}: HTTP ${r.status}`);
    return r.json();
  }));
  try { return await wasmCache.get(rel); } catch (e) { wasmCache.delete(rel); throw e; }
}
const wasmMissing = (e) => `<p class="err">The Wasm page data is not available here (${esc(e.message || e)}). ` +
  "It is written by <code>wasm-pages</code> (<code>make pages</code>) next to the page.</p>";
const wlink = (kind, slug, text) => `<a href="#/wasm-${kind}/${encodeURIComponent(slug)}">${esc(text)}</a>`;
const flink = (slug, idx, text) => `<a href="#/wasm-func/${encodeURIComponent(slug)}/${idx}">${esc(text)}</a>`;
const kindTag = (k) => `<span class="prov prov-browser" title="what this page is">${esc(k)}</span>`;
function runBadge(detail) {
  const t = "computed at build time by running Lean library code (not a kernel check)" + (detail ? ": " + detail : "");
  return `<span class="prov prov-run" title="${esc(t)}">Lean, runtime${detail ? ": " + esc(detail) : ""}</span>`;
}
const SYNTAX_CFG = "Syntactic block CFG — incomplete, not an execution model: flow edges follow structured control " +
  "(Silmaril.Wasm.Cfg.Edge, which the builder blockCfg is proved to compute), effect edges mark possible traps and raises; " +
  "no theorem says executions follow this graph.";
const SYNTAX_CALLS = "Syntactic call graph — read from the call instructions, not from execution: one edge per (caller, callee, kind), " +
  "call_indirect and call_ref go to explicit “unknown callee” nodes. Not proved to cover all runtime calls: no theorem links it to " +
  "Shape.RespectsCalls (the hypothesis under which closeD_eq_close_of_wf rules out divergence by recursion).";
// The block CFGs with a Lean kernel-checked dominator table (machine documents loaded by
// examples/project/ProjectSelfTest/WasmBlockCfg.lean), by module slug and function index.
const KERNEL_CFG = {
  "silmaril.wasm.examples.verified.prog/3": "silmaril.wasm.blockcfg.verified.sum",
  "silmaril.wasm.cfg.examples.mod/0": "silmaril.wasm.blockcfg.dispatch",
  "silmaril.wasm.cfg.examples.mod/1": "silmaril.wasm.blockcfg.specials",
  "silmaril.wasm.cfg.examples.effects/1": "silmaril.wasm.blockcfg.guarded",
  "silmaril.wasm.examples.rust_door/5": "silmaril.wasm.blockcfg.rust_door.enter",
};
function sourceDl(s, size) {
  const rows = [["kind", s.kind], ["name", s.name], ["registered CID (BLAKE3)", s.cid], ["registered SHA-256", s.sha256],
    ["path", s.path], ["size", size == null ? null : size + " B"], ["note", s.doc]];
  return "<dl>" + rows.filter(([, v]) => v != null && v !== "").map(([k, v]) => `<dt>${esc(k)}</dt><dd>${
    k === "registered CID (BLAKE3)" ? `<a href="${href("artifact", v)}">${esc(v)}</a>` : esc(v)}</dd>`).join("") + "</dl>";
}
// Downloads, the page's own SHA-256 of the downloaded bytes, and the WAT.
function filesBlock(slug, d) {
  let h = '<div class="controls">';
  if (d.hasBlob) h += `<a href="wasm/blob/${encodeURIComponent(slug)}.wasm" download>download .wasm</a>` +
    ` <button id="wsha">SHA-256 of the download</button> <span id="wshaout" class="muted"></span>`;
  else h += '<span class="muted">no bytes</span>';
  if (!/^not printed|^no WAT/.test(d.watNote || "")) h += ` · <a href="wasm/wat/${encodeURIComponent(slug)}.wat" target="_blank">WAT</a>`;
  h += `</div><p class="muted">WAT: ${esc(d.watNote || "")}</p>`;
  return h;
}
function wireSha(slug) {
  const b = $("#wsha");
  if (!b) return;
  b.addEventListener("click", async () => {
    $("#wshaout").textContent = "…";
    try {
      const buf = await (await fetch(`wasm/blob/${encodeURIComponent(slug)}.wasm`)).arrayBuffer();
      const h = [...new Uint8Array(await crypto.subtle.digest("SHA-256", buf))].map((x) => x.toString(16).padStart(2, "0")).join("");
      $("#wshaout").innerHTML = `<code>${h}</code> (${buf.byteLength} B, ${provBadge("browser")})`;
    } catch (e) { $("#wshaout").textContent = String(e.message || e); }
  });
}
function simpleTable(rows, cols) {
  if (!rows.length) return '<p class="muted">(none)</p>';
  return '<div class="tablebox"><table><thead><tr>' + cols.map(([c]) => `<th>${esc(c)}</th>`).join("") + "</tr></thead><tbody>" +
    rows.map((r) => "<tr>" + cols.map(([, f]) => `<td>${f(r)}</td>`).join("") + "</tr>").join("") + "</tbody></table></div>";
}
async function wasmPage() {
  let ix;
  try { ix = await wasmJson("index.json"); } catch (e) { return wasmMissing(e); }
  const top = (xs) => xs.filter((x) => !x.source.parent);
  const sub = (xs) => xs.filter((x) => x.source.parent);
  let h = "<h2>Wasm</h2><p>Components, core modules and their functions: the Wasm blobs of the artifact registry " +
    "(<code>silmaril/artifacts.toml</code>), the modules and components inside them, and example modules that are Lean values. " +
    `Decoded, printed and validated at build time by the Lean library (${runBadge()}); see each page for what is proved.</p>`;
  const compCols = [["component", (c) => wlink("component", c.slug, c.title)], ["size", (c) => c.size + " B"],
    ["imports", (c) => c.imports ?? ""], ["exports", (c) => c.exports ?? ""], ["core modules", (c) => c.modules ?? ""],
    ["components", (c) => c.components ?? ""], ["source", (c) => esc(c.source.kind)]];
  const modCols = [["module", (m) => wlink("module", m.slug, m.title)], ["size", (m) => m.size == null ? "" : m.size + " B"],
    ["functions", (m) => m.funcs ?? ""], ["defined", (m) => m.defined ?? ""], ["imports", (m) => m.imports ?? ""],
    ["exports", (m) => m.exports ?? ""], ["source", (m) => esc(m.source.kind)],
    ["inside", (m) => m.source.parent ? wlink("component", ix.components.find((c) => c.id === m.source.parent)?.slug || "", m.source.parent) : ""]];
  h += `<h2>Components (${top(ix.components).length} registered, ${sub(ix.components).length} nested)</h2>` + simpleTable(top(ix.components).concat(sub(ix.components)), compCols);
  h += `<h2>Core modules (${top(ix.modules).length} top-level, ${sub(ix.modules).length} inside components)</h2>` + simpleTable(top(ix.modules).concat(sub(ix.modules)), modCols);
  h += '<h2>Functions</h2><div class="controls"><input type="text" id="wfq" placeholder="filter by name, export or module" size="40"> <span id="wfn" class="muted"></span></div><div id="wfl"></div>';
  const init = async () => {
    let fs;
    try { fs = await wasmJson("functions.json"); } catch (e) { $("#wfl").innerHTML = wasmMissing(e); return; }
    const title = new Map(ix.modules.map((m) => [m.slug, m.title]));
    const show = () => {
      const q = $("#wfq").value.toLowerCase();
      const rows = fs.filter(([sl, , n, e]) => !q || [n, e, title.get(sl)].some((x) => x && x.toLowerCase().includes(q)));
      $("#wfn").textContent = `${rows.length} of ${fs.length} defined functions` + (rows.length > 300 ? " (first 300 shown)" : "");
      $("#wfl").innerHTML = simpleTable(rows.slice(0, 300), [["function", ([sl, i, n]) => flink(sl, i, n || `func ${i}`)],
        ["export", ([, , , e]) => e ? `<code>${esc(e)}</code>` : ""], ["blocks", ([, , , , b]) => b],
        ["module", ([sl]) => wlink("module", sl, title.get(sl) || sl)]]);
    };
    $("#wfq").addEventListener("input", show);
    show();
  };
  return { html: h, init, dispose: disposeWcy };
}
async function wasmComponentPage(slug) {
  let c, ix;
  try { [c, ix] = await Promise.all([wasmJson(`c/${slug}.json`), wasmJson("index.json")]); } catch (e) { return wasmMissing(e); }
  const s = c.summary;
  let h = `<h2>${kindTag("component")} <code>${esc(s.title)}</code></h2>`;
  h += crumbs(ix, s.source.parent);
  h += sourceDl(s.source, s.size) + filesBlock(s.slug, c);
  if (c.unsupported) return { html: h + `<p class="err">Unsupported: ${esc(c.unsupported)}</p>`, init: () => wireSha(s.slug) };
  h += `<p class="muted">Decoded by <code>Silmaril.Wasm.Component.Binary.parse</code> ${runBadge()}.</p>`;
  if (c.validity) h += `<p>component validation: <b>${esc(c.validity.status)}</b> ${runBadge()} <span class="muted">${esc(c.validity.note)}</span></p>`;
  h += "<h2>Children</h2>" + simpleTable(c.children, [["kind", (x) => esc(x.kind)], ["index", (x) => x.index],
    ["page", (x) => x.unsupported ? `<span class="err">${esc(x.unsupported)}</span>` : wlink(x.kind, x.slug, x.id)]]);
  const modSlug = (i) => (c.children.find((x) => x.kind === "module" && x.index === i) || {}).slug;
  h += "<h2>Core instances</h2>" + simpleTable(c.coreInstances.map((x, i) => Object.assign({ i }, x)), [["#", (x) => x.i],
    ["kind", (x) => esc(x.kind)],
    ["what", (x) => x.kind === "instantiate"
      ? "instantiate " + (modSlug(x.module) ? wlink("module", modSlug(x.module), "core module " + x.module) : "core module " + x.module) +
        (x.args.length ? " with " + x.args.map(([n, i]) => `${esc(n)} = core instance ${i}`).join(", ") : "")
      : "exports " + x.names.map(esc).join(", ")]]);
  if (c.instances.length) h += "<h2>Component instances</h2>" + simpleTable(c.instances, [["kind", (x) => esc(x.kind)],
    ["what", (x) => x.kind === "instantiate" ? `instantiate component ${x.component}` + (x.args.length ? " with " + x.args.map(esc).join(", ") : "") : "exports " + x.names.map(esc).join(", ")]]);
  h += "<h2>Imports</h2>" + simpleTable(c.imports, [["name", (x) => `<code>${esc(x.name)}</code>`], ["kind", (x) => esc(x.kind)]]);
  h += "<h2>Exports</h2>" + simpleTable(c.exports, [["name", (x) => `<code>${esc(x.name)}</code>`], ["sort", (x) => esc(x.kind)], ["index", (x) => x.idx]]);
  if (c.canons.length) h += "<h2>Canonical functions</h2>" + simpleTable(c.canons.map((t) => ({ t })), [["canon", (x) => `<code>${esc(x.t)}</code>`]]);
  if (c.world) h += "<h2>Interface (world)</h2>" + (c.world.text ? `<p class="muted">${esc(c.world.note)} ${runBadge()}</p><pre class="code">${esc(c.world.text)}</pre>`
    : `<p class="muted">${esc(c.world.note)}</p>`);
  h += "<h2>WIT</h2>" + (c.wit.text ? `<p class="muted">${esc(c.wit.note)}</p><pre class="code">${esc(c.wit.text)}</pre>`
    : `<p class="muted">${esc(c.wit.note)}</p>`);
  if (c.customs.length) h += `<p class="muted">custom sections: ${c.customs.map(esc).join(", ")}</p>`;
  return { html: h, init: () => wireSha(s.slug) };
}
function graphStyle(extra) {
  return [{ selector: "node", style: { label: "data(label)", "text-wrap": "wrap", "text-max-width": 260, "font-size": 12,
      "text-valign": "center", "text-halign": "center", shape: "round-rectangle", width: "label", height: "label", padding: 8,
      "background-color": "#fff", "border-width": 1.5, "border-color": "#2f5d9e", color: "#1d2329" } },
    { selector: "node[kind = 'import']", style: { "border-style": "dashed", "border-color": "#8a939c", "background-color": "#f4f6f8" } },
    { selector: "node[kind = 'unknown']", style: { shape: "diamond", "border-color": "#d9a400", "background-color": "#fff6dc", padding: 14 } },
    { selector: "node[kind = 'special']", style: { "border-color": "#d64545" } },
    { selector: "node[kind = 'exit']", style: { "border-color": "#2e9d4f", "border-width": 3 } },
    { selector: "node[entry = 1]", style: { "border-width": 4 } },
    { selector: "node[focus = 1]", style: { "underlay-color": "#f2c94c", "underlay-opacity": 0.6, "underlay-padding": 6 } },
    { selector: "edge", style: { label: "data(label)", "font-size": 10, "curve-style": "bezier", "target-arrow-shape": "triangle", width: 1.3,
      "line-color": "#8a939c", "target-arrow-color": "#8a939c", "text-background-color": "#fbfbfa", "text-background-opacity": 0.85 } },
    { selector: "edge[kind = 'effect']", style: { "line-style": "dashed", "line-color": "#d64545", "target-arrow-color": "#d64545", color: "#b03030" } },
    { selector: "edge[kind = 'tail']", style: { "line-style": "dotted" } },
    { selector: "edge[back = 1]", style: { "line-color": "#2f5d9e", "target-arrow-color": "#2f5d9e", width: 2 } },
    { selector: ":selected", style: { "overlay-color": "#2f5d9e", "overlay-opacity": 0.2 } }].concat(extra || []);
}
function zoomControls() {
  return '<button id="wfit">fit</button><button id="wzin">+</button><button id="wzout">−</button>';
}
function wireZoomButtons() {
  $("#wfit").addEventListener("click", () => wcy && wcy.fit(undefined, 30));
  $("#wzin").addEventListener("click", () => wcy && wcy.zoom({ level: wcy.zoom() * 1.3, renderedPosition: { x: wcy.width() / 2, y: wcy.height() / 2 } }));
  $("#wzout").addEventListener("click", () => wcy && wcy.zoom({ level: wcy.zoom() / 1.3, renderedPosition: { x: wcy.width() / 2, y: wcy.height() / 2 } }));
}
// A large graph fitted to the box is unreadable: then start at a readable zoom on the entry.
function wireZoom(focusId, top) {
  if (wcy.zoom() >= 0.55) return;
  const n = focusId && wcy.getElementById(focusId);
  wcy.zoom(0.85);
  if (!n || !n.length) { wcy.center(); return; }
  if (top) { const p = n.position(); wcy.pan({ x: wcy.width() / 2 - p.x * 0.85, y: 50 - p.y * 0.85 }); }
  else wcy.center(n);
}
// "inside A › B" links from a module or component up to its top-level component.
function crumbs(ix, parentId) {
  const out = [];
  for (let id = parentId; id;) {
    const c = ix.components.find((x) => x.id === id);
    if (!c) { out.unshift(esc(id)); break; }
    out.unshift(wlink("component", c.slug, c.title));
    id = c.source.parent;
  }
  return out.length ? `<p>inside ${out.join(" › ")}</p>` : "";
}
function fname(f) { return f.display || f.name || (f.imported ? f.import : `func ${f.idx}`); }
async function wasmModulePage(slug) {
  let m, ix;
  try { [m, ix] = await Promise.all([wasmJson(`m/${slug}.json`), wasmJson("index.json")]); } catch (e) { return wasmMissing(e); }
  const s = m.summary;
  let h = `<h2>${kindTag("core module")} <code>${esc(s.title)}</code></h2>`;
  h += crumbs(ix, s.source.parent);
  h += sourceDl(s.source, s.size) + filesBlock(s.slug, m);
  if (m.unsupported) return { html: h + `<p class="err">Unsupported: ${esc(m.unsupported)}</p>`, init: () => wireSha(s.slug) };
  const v = m.validity;
  h += `<p>validation: <b>${esc(v.status)}</b> ${v.status === "valid" || v.status === "rejected" ? runBadge(v.note) : `<span class="muted">${esc(v.note)}</span>`}</p>`;
  const nCalls = m.calls.length, unknown = m.calls.filter((c) => typeof c[1] === "string").length;
  h += `<h2>Call graph</h2><p class="muted">${esc(SYNTAX_CALLS)}</p>`;
  h += `<div class="controls"><label>focus <select id="wfocus" style="max-width:420px"><option value="">whole module</option>${m.functions.filter((f) => !f.imported).map((f) =>
    `<option value="${f.idx}">${esc(f.idx + " " + fname(f))}</option>`).join("")}</select></label>` +
    `<label><input type="checkbox" id="wimports" checked> imports</label> ${zoomControls()}` +
    `<span class="muted">${nCalls} edges (${unknown} to unknown callees); click a function to open it. Dashed: imported; diamond: unknown callee.</span></div>`;
  h += '<div id="wcy" style="height:70vh;min-height:420px;border:1px solid var(--line);background:var(--panel)"></div>';
  if (m.addressTaken.length) h += `<p class="muted">Address-taken functions (element segments, <code>ref.func</code>), the syntactic candidates of indirect calls (not resolved): ${
    m.addressTaken.map((i) => { const f = m.functions[i]; return f && !f.imported ? flink(s.slug, i, i + " " + fname(f)) : esc(i); }).join(", ")}</p>`;
  h += "<h2>Functions</h2>" + simpleTable(m.functions, [["idx", (f) => f.idx],
    ["name", (f) => f.imported ? `<span class="muted">import</span> <code>${esc(f.import)}</code>` : flink(s.slug, f.idx, fname(f))],
    ["export", (f) => f.export ? `<code>${esc(f.export)}</code>` : ""], ["signature", (f) => `<code>${esc(f.sig)}</code>`],
    ["instrs", (f) => f.instrs ?? ""], ["blocks", (f) => f.blocks ?? ""], ["effect marks", (f) => (f.effects || []).map(esc).join(", ")]]);
  h += "<h2>Imports</h2>" + simpleTable(m.imports, [["module", (x) => `<code>${esc(x.module)}</code>`], ["name", (x) => `<code>${esc(x.name)}</code>`], ["kind", (x) => esc(x.kind)]]);
  h += "<h2>Exports</h2>" + simpleTable(m.exports, [["name", (x) => `<code>${esc(x.name)}</code>`], ["kind", (x) => esc(x.kind)],
    ["index", (x) => x.kind === "func" && m.functions[x.idx] && !m.functions[x.idx].imported ? flink(s.slug, x.idx, String(x.idx)) : x.idx]]);
  if (m.start != null) h += `<p>start function: ${flink(s.slug, m.start, String(m.start))}</p>`;
  if (m.embeddedWorld) h += "<h2>Embedded world (WIT)</h2>" + (m.embeddedWorld.text
    ? `<p class="muted">${esc(m.embeddedWorld.note)} ${runBadge()}</p><pre class="code">${esc(m.embeddedWorld.text)}</pre>`
    : `<p class="muted">${esc(m.embeddedWorld.note)}</p>`);
  const init = () => {
    wireSha(s.slug);
    const draw = () => {
      if (wcy) wcy.destroy();
      const focus = $("#wfocus").value, withImports = $("#wimports").checked;
      let edges = m.calls.map(([a, b, kind, n]) => ({ a, b: typeof b === "string" ? "u:" + b : b, kind, n }));
      if (!withImports) edges = edges.filter((e) => typeof e.b !== "number" || !m.functions[e.b].imported);
      if (focus !== "") { const f = Number(focus); edges = edges.filter((e) => e.a === f || e.b === f); }
      const ids = new Set(edges.flatMap((e) => [e.a, e.b]));
      if (focus !== "") ids.add(Number(focus));
      else for (const f of m.functions) if (!f.imported) ids.add(f.idx);
      const els = [...ids].map((id) => {
        if (typeof id === "string") return { data: { id: "n" + id, label: id.slice(2).replace(": ", "\n"), kind: "unknown" } };
        const f = m.functions[id];
        return { data: { id: "n" + id, idx: id, label: `${id} ${fname(f)}` + (f.export ? `\nexport ${f.export}` : ""),
          kind: f.imported ? "import" : "defined", focus: String(id) === focus ? 1 : 0 } };
      });
      edges.forEach((e, i) => els.push({ data: { id: "e" + i, source: "n" + e.a, target: "n" + e.b, kind: e.kind,
        label: (e.kind === "direct" ? "" : e.kind) + (e.n > 1 ? ` ×${e.n}` : "") } }));
      wcy = cytoscape({ container: $("#wcy"), elements: els, minZoom: 0.05, maxZoom: 3, wheelSensitivity: 0.25, style: graphStyle(),
        layout: { name: "dagre", rankDir: "LR", nodeSep: 18, rankSep: 70, animate: false } });
      wcy.on("tap", "node", (ev) => { const i = ev.target.data("idx"); if (i != null && !m.functions[i].imported) location.hash = `#/wasm-func/${encodeURIComponent(s.slug)}/${i}`; });
      wireZoom(focus !== "" ? "n" + focus : null);
    };
    wireZoomButtons();
    $("#wfocus").addEventListener("change", draw);
    $("#wimports").addEventListener("change", draw);
    if (m.functions.length > 80) {
      // large modules start focused on the first exported function
      const f = m.functions.find((x) => !x.imported && x.export);
      if (f) $("#wfocus").value = String(f.idx);
    }
    draw();
  };
  return { html: h, init, dispose: disposeWcy };
}
async function wasmFuncPage(arg) {
  // #/wasm-func/<module slug>/<function index>[/@<variant>][/<node>]: the graph variant (a key of
  // cfg.variants, or "top" for the top-level graph) and the selected node (b<k>, exit, trap, raise, invalid).
  const am = /^(.*)\/(\d+)(?:\/@([A-Za-z0-9._-]+))?(?:\/(b\d+|n\d+|exit|trap|raise|invalid))?$/.exec(arg) || [null, arg, "NaN", null, null];
  const slug = am[1], idx = Number(am[2]), askedVariant = am[3] || null, focusId = am[4] || null;
  let m, ix;
  try { [m, ix] = await Promise.all([wasmJson(`m/${slug}.json`), wasmJson("index.json")]); } catch (e) { return wasmMissing(e); }
  const f = m.functions[idx], body = (m.bodies || []).find((b) => b.idx === idx);
  if (!f || !body) return `<p class="err">no defined function ${esc(idx)} in ${esc(slug)}</p>`;
  const s = m.summary, top = body.cfg;
  // Graph variants (issue #231): the top-level graph is the explicit-sink model unless `model` says
  // otherwise; `variants` are other graphs of the same body, `default` names the one shown first.
  // Nothing here derives a variant: each is drawn exactly as the page data gives it.
  const variants = Object.fromEntries(Object.entries(top.variants && typeof top.variants === "object" ? top.variants : {})
    .filter(([k, v]) => k !== "top" && /^[A-Za-z0-9._-]+$/.test(k) && v && Array.isArray(v.edges)));
  const has = (k) => k != null && Object.hasOwn(variants, k);
  // An unknown variant in a link falls back to the data's default, like no variant.
  const vname = askedVariant === "top" ? "top" : has(askedVariant) ? askedVariant : has(top.default) ? top.default : "top";
  const V = vname === "top" ? top : variants[vname];
  // An instruction-level graph's nodes must each name an instruction (or the terminator slot) of a block.
  function validNodes(v) {
    const bs = v.blocks || top.blocks;
    return Array.isArray(v.nodes) && v.nodes.every((nd) => Array.isArray(nd) && Number.isInteger(nd[0]) && Number.isInteger(nd[1]) &&
      bs[nd[0]] && nd[1] >= 0 && nd[1] <= bs[nd[0]].instrs.length);
  }
  const cfg = { model: V.model || (vname === "top" ? "explicit-sink" : "unspecified"), label: V.label, note: V.note, relation: V.relation,
    entry: V.entry, blocks: (V.blocks || top.blocks).map((b) => ({ instrs: [], effects: [], ...b })), edges: V.edges || [], bases: V.bases,
    members: Array.isArray(V.blocks) && Array.isArray(V.members) ? V.members : null,
    granularity: V.granularity === "instr" && validNodes(V) ? "instr" : "block", nodes: V.nodes,
    outcomes: Array.isArray(V.outcomes) ? V.outcomes : [] };
  // Graphs at the other granularity over the same blocks: the "expand to instructions" and
  // "back to blocks" links of the inspector (only when the data has such a graph).
  const sameBlocks = (v) => !v.blocks || v.blocks === top.blocks;
  const graphs = [["top", top]].concat(Object.entries(variants));
  const instrGraph = graphs.find(([, v]) => v.granularity === "instr" && validNodes(v) && sameBlocks(v));
  const blockGraph = graphs.find(([, v]) => v.granularity !== "instr" && sameBlocks(v) && (v.model || "explicit-sink") === cfg.model)
    || graphs.find(([, v]) => v.granularity !== "instr" && sameBlocks(v));
  // A graph with its own blocks may say which shared-numbering blocks each of its blocks contains
  // (`members`, e.g. maximal basic blocks); the inspector links both ways. Nothing is merged here.
  const memberGraph = graphs.find(([, v]) => Array.isArray(v.blocks) && Array.isArray(v.members) && v.granularity !== "instr");
  const containerOf = (bi) => memberGraph && sameBlocks(V) ? memberGraph[1].members.findIndex((ms) => Array.isArray(ms) && ms.includes(bi)) : -1;
  const legacy = vname === "top" && cfg.model === "explicit-sink";
  let h = `<h2>${kindTag("function")} <code>${esc(fname(f))}</code> <span class="muted">(function ${idx} of ${wlink("module", s.slug, s.title)})</span></h2>`;
  h += crumbs(ix, s.source.parent);
  h += "<dl>" + [["symbol", f.display ? f.name + " (demangled above by wasm-tools demangle in Lean)" : null], ["signature", f.sig], ["export", f.export], ["locals", f.locals], ["instructions", f.instrs], ["basic blocks", f.blocks],
    ["effect marks", (f.effects || []).join(", ") || "none"]].filter(([, v]) => v != null).map(([a, b]) => `<dt>${esc(a)}</dt><dd>${esc(b)}</dd>`).join("") + "</dl>";
  const callers = m.calls.filter((c) => c[1] === idx).map((c) => c[0]), callees = m.calls.filter((c) => c[0] === idx);
  h += `<p>calls: ${callees.length ? callees.map(([, b, kind, n]) => typeof b === "string" ? `<span class="prov prov-gen">${esc(b)}</span>` :
    (m.functions[b].imported ? `<code>${esc(m.functions[b].import)}</code>` : flink(s.slug, b, fname(m.functions[b]))) + (kind !== "direct" ? ` (${esc(kind)})` : "") + (n > 1 ? ` ×${n}` : "")).join(", ") : "none"}` +
    ` · called by: ${callers.length ? callers.map((a) => flink(s.slug, a, fname(m.functions[a]))).join(", ") : "no call instruction in this module"} <span class="muted">(syntactic)</span></p>`;
  const kc = legacy ? KERNEL_CFG[`${s.slug}/${idx}`] : null;
  // The edges as written by wasm-pages: `flow` edges are Cfg.Edge (blockCfg), `effect` edges are
  // the "may" edges of Cfg.EffectEdge. Every edge stays in `E`, whatever is drawn: the inspector,
  // the counts and the dominators read `E`, never the drawn graph.
  // Nodes: one per block (b<k>), or, for an instruction-level graph, one per instruction (n<k>,
  // nodes[k] = [block, position], the position after the last instruction being the terminator).
  const instrG = cfg.granularity === "instr";
  const nid = (k) => (instrG ? "n" : "b") + k;
  const isNode = (id) => typeof id === "string" && /^[bn]\d+$/.test(id);
  const nodeIds = Array.from({ length: instrG ? cfg.nodes.length : cfg.blocks.length }, (_, k) => nid(k));
  const blockOf = (id) => instrG ? cfg.nodes[Number(id.slice(1))][0] : Number(id.slice(1));
  const instrAt = (k) => { const [bi, at] = cfg.nodes[k], bl = cfg.blocks[bi]; return at < bl.instrs.length ? bl.instrs[at] : bl.term || "(falls through)"; };
  const tid = (t) => typeof t === "number" ? nid(t) : t;
  const E = cfg.edges.map(([a, t, kind], i) => ({ i, src: nid(a), a, tgt: tid(t), may: kind === "effect", kind }));
  // Outcomes: what a node may do that is not an edge (all-effects models: trap, raise with its
  // handler — a node, "caller" or "unresolved"). They are in no dominator basis.
  const O = cfg.outcomes.filter((o) => Array.isArray(o) && typeof o[0] === "number" && typeof o[1] === "string")
    .map(([n, effect, handler, member], i) => ({ i, src: nid(n), effect, handler: typeof handler === "number" ? nid(handler) : handler == null ? null : String(handler),
      member: typeof member === "number" ? member : null }));
  const outcomesOf = (id) => O.filter((o) => o.src === id);
  const oText = (o) => o.effect + (o.handler ? " → " + o.handler : "");
  const flowE = E.filter((e) => !e.may), mayE = E.filter((e) => e.may);
  const kinds = [...new Set(E.map((e) => e.kind))];
  const outOf = new Map(), into = new Map();
  for (const e of E) {
    if (!outOf.has(e.src)) outOf.set(e.src, []); outOf.get(e.src).push(e);
    if (!into.has(e.tgt)) into.set(e.tgt, []); into.get(e.tgt).push(e);
  }
  const mayTgts = (id) => (outOf.get(id) || []).filter((e) => e.may).map((e) => e.tgt);
  const cnt = (xs, t) => xs.filter((e) => e.tgt === t).length;
  const C = { flow: E.filter((e) => e.kind === "flow").length, may: mayE.length, flowTrap: cnt(flowE, "trap"), flowRaise: cnt(flowE, "raise"),
    mayTrap: cnt(mayE, "trap"), mayRaise: cnt(mayE, "raise"), marked: nodeIds.filter((id) => (!instrG && cfg.blocks[blockOf(id)].effects.length) || outcomesOf(id).length).length,
    mayFrom: new Set(mayE.map((e) => e.src)).size };
  const specials = ["exit", "trap", "raise", "invalid"].filter((t) => t === "exit" || into.has(t) || cfg.entry === t);
  // Special nodes in dominator trees: all four for the explicit-sink graph (as its kernel tables),
  // otherwise only those the graph has.
  // Dominator bases: named edge sets (by kind), from the data or, when it names none, flow edges
  // (the default) and flow + effect. Each tree is computed on its own basis, whatever is drawn.
  const BASES = (Array.isArray(cfg.bases) && cfg.bases.length ? cfg.bases : [{ id: "flow", kinds: ["flow"] },
    { id: "flow+effect", kinds: ["flow", "effect"], kernelTable: kc || undefined }])
    .filter((b) => b && typeof b.id === "string" && Array.isArray(b.kinds));
  const basisDefault = (BASES.find((b) => b.default) || BASES[0]).id;
  const basisOf = (id) => BASES.find((b) => b.id === id);
  const basisEdges = (id) => E.filter((e) => basisOf(id).kinds.includes(e.kind));
  const basisText = (id) => { const b = basisOf(id); return b.label || b.kinds.join(" + ") + (b.kinds.length === 1 ? " edges" : ""); };
  const domNodes = nodeIds.concat(legacy ? ["exit", "trap", "raise", "invalid"] : specials);
  const domEntry = tid(cfg.entry);
  const DOM = Object.fromEntries(BASES.map((b) => [b.id, dominators(domNodes, basisEdges(b.id).map((e) => [e.src, e.tgt]), [domEntry])]));
  const domName = (n) => n === undefined ? "unreached" : n === null ? "root" : n;
  const vlabel = vname === "top" ? `top-level graph (${cfg.model})` : `${vname}${cfg.label ? " — " + cfg.label : ""} (${cfg.model})`;
  h += `<h2 id="wcfg">Control-flow graph (${instrG ? "one node per instruction, boxed by basic block" : "basic blocks"})</h2>`;
  if (Object.keys(variants).length) h += `<div class="controls"><label>graph <select id="wvariant" aria-label="Graph variant">` +
    [["top", `top-level graph (${top.model || "explicit-sink"})`]].concat(Object.entries(variants).map(([k, v]) => [k, `${k}${v.label ? " — " + v.label : ""} (${v.model || "unspecified"})`]))
      .map(([k, l]) => `<option value="${esc(k)}"${k === vname ? " selected" : ""}>${esc(l)}</option>`).join("") + "</select></label>" +
    `<span class="muted" id="wvariantnote">${(has(top.default) ? esc(top.default) : "the top-level graph")} is shown first, as the page data says. ` +
    `Each graph is drawn exactly as the data gives it; switching changes the drawn graph and its dominator bases.</span></div>`;
  if (legacy) {
    h += `<p class="muted">${esc(SYNTAX_CFG)}</p>`;
    h += `<p>blocks and flow edges: ${runBadge("Silmaril.Wasm.Cfg.blockCfg, proved to compute Edge (blockCfg_eq, edge_iff)")}` +
      (kc ? ` · machine document ${link("machine", kc)}: its kernel-checked dominator table is over flow + effect edges; the dominator view checks that it is this graph and compares it` : "") + "</p>";
  } else {
    h += `<p id="wvariantinfo">graph: <b>${esc(vlabel)}</b>, as written in the page data. ` +
      (cfg.relation ? `Intended relation: <code>${esc(cfg.relation)}</code> <span class="muted">(metadata from the data, not checked here)</span>. ` : "") +
      (cfg.note ? esc(cfg.note) + " " : "") +
      `<span class="muted">No theorem shown on this page says that executions follow this graph.</span></p>`;
  }
  // Legend with exact counts: what each mark means, and that the may-edges are not drawn by default.
  const sw = (style) => `<svg width="34" height="10" aria-hidden="true"><line x1="1" y1="5" x2="33" y2="5" style="${style}"/></svg>`;
  h += `<div class="legend wlegend" id="wlegend" role="note" aria-label="Legend and edge counts">` +
    `<span>${sw("stroke:#8a939c;stroke-width:1.5")} flow <b data-c="flow">${C.flow}</b></span>` +
    `<span>${sw("stroke:#2f5d9e;stroke-width:2")} back edge (to an earlier block)</span>` +
    (C.flowTrap + C.flowRaise ? `<span>${sw("stroke:#b42318;stroke-width:2.5")} control edge to trap/raise <b data-c="flowSpecial">${C.flowTrap + C.flowRaise}</b>` +
      ` <span class="muted">(the terminator is <code>unreachable</code>, <code>throw</code> or <code>throw_ref</code>)</span></span>` : "") +
    (C.may || legacy ? `<span>${sw("stroke:#d64545;stroke-width:1.2;stroke-dasharray:4 3")} may-edge <b data-c="may">${C.may}</b> ` +
    `<span class="muted">(<span data-c="mayTrap">${C.mayTrap}</span> to trap, <span data-c="mayRaise">${C.mayRaise}</span> to raise, ` +
    `from <span data-c="mayFrom">${C.mayFrom}</span> of ${nodeIds.length} ${instrG ? "nodes" : "blocks"})</span></span>` : "") +
    kinds.filter((k) => k !== "flow" && k !== "effect").map((k) => `<span>${sw("stroke:#8a939c;stroke-width:1.5;stroke-dasharray:1 3")} ${esc(k)} ` +
      `<b data-c="kind:${esc(k)}">${E.filter((e) => e.kind === k).length}</b></span>`).join("") +
    (O.length ? `<span>${sw("stroke:#7c3aed;stroke-width:1.2;stroke-dasharray:2 2")} outcomes <b data-c="outcomes">${O.length}</b> <span class="muted">(` +
      [...new Set(O.map((o) => o.effect))].map((e) => `${O.filter((o) => o.effect === e).length} ${esc(e)}`).join(", ") +
      `; ${O.filter((o) => isNode(o.handler)).length} to a handler, ${O.filter((o) => o.handler === "caller").length} to the caller, ` +
      `${O.filter((o) => o.handler && !isNode(o.handler) && o.handler !== "caller").length} other; not edges, in no dominator basis)</span></span>` : "") +
    `<span><span class="wbadge">⚠</span> marks on <b data-c="marked">${C.marked}</b> ${instrG ? "nodes" : "blocks"}</span></div>`;
  if (C.may || legacy) h += `<p class="muted" id="wmaynote">May-edges are conservative and syntactic: a block that contains an instruction that may trap ` +
    `(division, memory, table, cast, …) or a call gets one to <code>trap</code> (and a call one to <code>raise</code>). ` +
    `They are summarised as <span class="wbadge">⚠</span> marks on their blocks and drawn for the block you select or hover, or all at once. ` +
    `An unmarked block is not shown to be trap-free: no theorem about executions is recorded here.</p>`;
  h += `<div class="controls" role="toolbar" aria-label="Graph view"><button id="wflat" aria-pressed="true">Flat CFG</button><button id="wdom" aria-pressed="false">Dominator tree</button>` +
    `<label title="Draw every may-edge${O.length ? " and handler link" : ""} (otherwise only the selected or hovered node's)"><input type="checkbox" id="weff"> draw all may-edges${O.length ? " and handler links" : ""}</label>` +
    `<label>dominator basis <select id="wbasis">` + BASES.map((b) => `<option value="${esc(b.id)}"${b.id === basisDefault ? " selected" : ""}>` +
      `${esc(basisText(b.id))} (${basisEdges(b.id).length})</option>`).join("") + `</select></label>` +
    `<label>${instrG ? "node" : "block"} <select id="wgo" aria-label="Select a node"><option value="">—</option>` +
    nodeIds.map((id, k) => `<option value="${id}">${id}${instrG ? ` (b${cfg.nodes[k][0]}) ${esc(instrAt(k))}` :
      `${cfg.blocks[k].effects.length ? " ⚠" : ""} → ${esc(cfg.blocks[k].term || "falls through")}`}${outcomesOf(id).length ? " ⚡" : ""}</option>`).join("") +
    specials.map((t) => `<option value="${t}">${t}</option>`).join("") + `</select></label>` +
    `${zoomControls()} <span id="wprov"></span></div>`;
  h += '<div id="wgraphwrap" style="display:flex;gap:12px;height:72vh;min-height:440px">' +
    '<div id="wcy" tabindex="0" role="application" aria-label="Control-flow graph. Keys: j or k next or previous block, ' +
    'arrow down or up first successor or predecessor, e draws all may-edges, plus and minus zoom, 0 fits, Escape clears the selection." ' +
    'aria-describedby="wkeys" style="flex:1 1 auto;border:1px solid var(--line);background:var(--panel);min-width:0"></div>' +
    '<div id="wside" aria-live="polite" style="flex:0 0 360px;overflow:auto;border:1px solid var(--line);background:var(--panel);padding:8px 10px" class="muted">' +
    'Click a block (or pick one above) for its instructions, edges and typing.</div></div>' +
    '<p class="muted" id="wkeys" style="font-size:12px">Keys on the focused graph: <kbd>j</kbd>/<kbd>k</kbd> next/previous block, ' +
    '<kbd>↓</kbd>/<kbd>↑</kbd> first successor/predecessor, <kbd>e</kbd> draw all may-edges, <kbd>+</kbd>/<kbd>−</kbd> zoom, <kbd>0</kbd> fit, <kbd>Esc</kbd> clear. ' +
    'Selecting a block updates the address bar to a direct link.</p>';
  h += `<h2>WAT</h2><p class="muted">printed from the decoded AST by Silmaril's printer (Silmaril.Wasm.Tools.Gen.Cmd.Print) ${runBadge()}</p><pre class="code">${esc(body.wat)}</pre>`;
  h += `<h2>Semantics (statements, not decided facts)</h2><ul class="muted">` +
    "<li>This function's behaviours are those of the Core 3.0 semantics. <code>Silmaril.Wasm.Abstract.WasmFunRef</code> " +
    "(address, profile, host) is its projection to an abstract function, proved to preserve and reflect equal behaviours " +
    "(<code>preserves_behEq</code>, <code>reflects_behEq</code>) and trap ≈ divergence (<code>preserves_trapDivEq</code>, " +
    "<code>reflects_trapDivEq</code>); <code>image_wasmFun</code> ties <code>wasmFun</code> to <code>behaviours</code>.</li>" +
    "<li>Whether this function may trap, diverge, or is deterministic (<code>AFun.MayTrap</code>, <code>MayDiv</code>, <code>Det</code>, …) " +
    "is an open statement here: no theorem about this function is recorded. The effect marks above are syntactic “may” marks.</li>" +
    "<li>Abstract bodies <code>Silmaril.Wasm.Abstract.Body.BodyM</code> form a lawful Elgot monad (<code>bodyM_lawfulElgot</code>); " +
    "they are a deterministic-given-inputs submodel (<code>toAFun_det</code>; <code>exists_not_denoted</code>: some nondeterministic " +
    "trace-set functions are denoted by no body), so their facts are not facts about arbitrary trace-set semantics. " +
    "Open: no concrete Core 3.0 body is yet proved to realise either model, so this CFG is not connected to them.</li></ul>";
  const instrN = (b) => `${b.instrs.length} instr${b.instrs.length === 1 ? "" : "s"}`;
  // Node label: what the block is and how it ends; a second line only for blocks with marks.
  // One line per node: each distinct outcome once, with its count when it repeats.
  const oLine = (id) => {
    const os = outcomesOf(id); if (!os.length) return "";
    const c = new Map(); for (const o of os) c.set(oText(o), (c.get(oText(o)) || 0) + 1);
    return "\n⚡ " + [...c].map(([k, n]) => (n > 1 ? n + "× " : "") + k).join(", ");
  };
  const blockLabel = (b, i) => `b${i} · ${instrN(b)} → ${b.term || "falls through"}` +
    (b.effects.length && !(outcomesOf("b" + i).length && !legacy) ? `\n⚠ ${b.effects.join(", ")}${mayTgts("b" + i).length ? " ⇢ " + mayTgts("b" + i).join("/") : ""}` : "") + oLine("b" + i);
  const instrLabel = (k) => `n${k} ${instrAt(k)}` + (mayTgts("n" + k).length ? "\n⇢ " + mayTgts("n" + k).join("/") : "") + oLine("n" + k);
  const nodeLabel = (id) => instrG ? instrLabel(Number(id.slice(1))) : blockLabel(cfg.blocks[Number(id.slice(1))], Number(id.slice(1)));
  const specialLabel = (t) => {
    if (t === "exit") return "exit";
    const f = (into.get(t) || []).filter((e) => !e.may).length, y = (into.get(t) || []).filter((e) => e.may).length;
    return t + (f || y ? `\n${[f ? f + " control" : "", y ? y + " may" : ""].filter(Boolean).join(" · ")}` : "");
  };
  const labelOf = (n) => isNode(n) ? (instrG ? `b${blockOf(n)}: ` : "") + nodeLabel(n) : specialLabel(n);
  const vpart = vname !== "top" || askedVariant === "top" ? "/@" + vname : "";
  const permalink = (id) => `#/wasm-func/${encodeURIComponent(s.slug)}/${idx}${vpart}${id ? "/" + id : ""}`;
  const init = async () => {
    // A basis's kernel-checked table (a machine document whose dominator table the registry proves)
    // counts only if the document is this graph on this basis: the same nodes (a block's state
    // name starts "b<k> [<path>].<pos>:"), the same entry, exactly the basis's edges (by kind),
    // and a table equal node by node to the browser's tree. Otherwise the page says what differs.
    const KT = {};
    for (const b of BASES) if (b.kernelTable) try {
      const r = (await q("SELECT canonical, dominators, dominator_theorem FROM machines WHERE name = ?", [b.kernelTable]))[0];
      if (!r || !r.dominators) { KT[b.id] = { name: b.kernelTable, why: "no kernel-checked table in this database" }; continue; }
      const doc = JSON.parse(r.canonical), names = new Map();
      for (const st of doc.states) { const mm = /^(b\d+) \[([^\]]*)\]\.(\d+):/.exec(st); names.set(st, mm ? mm[1] : st);
        if (mm) { const bl = cfg.blocks[Number(mm[1].slice(1))]; if (!bl || bl.path !== mm[2] || String(bl.pos) !== mm[3]) names.set(st, "?" + st); } }
      const short = (x) => x == null ? null : names.has(x) ? names.get(x) : "?" + x;
      const nodesOk = doc.states.length === domNodes.length && doc.states.every((x) => domNodes.includes(short(x)));
      const entryOk = ((doc.layers || {}).initial || []).length === 1 && short(doc.layers.initial[0]) === domEntry;
      const key = (a, k, c) => `${a}|${k}|${c}`;
      const mine = new Set(basisEdges(b.id).map((e) => key(e.src, e.kind, e.tgt))), theirs = new Set(doc.edges.map(([a, k, c]) => key(short(a), k, short(c))));
      const edgesOk = mine.size === theirs.size && [...mine].every((x) => theirs.has(x));
      const t = new Map(Object.entries(JSON.parse(r.dominators)).map(([k, v]) => [short(k), short(v)]));
      const tableOk = t.size === domNodes.length && domNodes.every((n) => t.has(n) && t.get(n) === (DOM[b.id].idom.get(n) ?? null));
      const why = [!nodesOk && "its nodes", !entryOk && "its entry", !edgesOk && "its edges", !tableOk && "its table"].filter(Boolean);
      KT[b.id] = { name: b.kernelTable, thm: r.dominator_theorem, same: !why.length, why: why.length ? "differs in " + why.join(", ") : "" };
    } catch (e) { KT[b.id] = { name: b.kernelTable, why: "could not be read (" + (e.message || e) + ")" }; }
    let view = "flat", sel = focusId && (domNodes.includes(focusId) ? focusId : null), hov = null, flatPos = null;
    const mayEls = () => wcy.edges(".may");
    // Which may-edges are drawn: all, or those of the selected and hovered node (in or out).
    const applyMay = () => {
      if (view !== "flat" || !wcy) return;
      const all = $("#weff").checked;
      wcy.batch(() => mayEls().forEach((e) => {
        const d = e.data();
        e.toggleClass("show", all || d.source === sel || d.target === sel || d.source === hov || d.target === hov);
      }));
    };
    const nodeBtn = (n) => `<button type="button" class="wnode" data-n="${esc(n)}">${esc(n)}</button>`;
    const edgeList = (es, end) => es.length ? '<span class="wedges">' + es.map((e) => nodeBtn(e[end])).join(" ") + "</span>" : '<span class="muted">none</span>';
    const inspect = (id) => {
      const side = $("#wside");
      side.classList.remove("muted");
      const ins = into.get(id) || [], outs = outOf.get(id) || [];
      const basis = $("#wbasis").value, di = DOM[basis].idom.get(id);
      let x = `<p style="margin:0 0 6px"><a href="${permalink(id)}" title="direct link to this node">#</a> `;
      const domLine = `immediate dominator (${esc(basisText(basis))}): ` +
        (di === undefined ? '<span class="muted">not reached from the entry on this basis</span>' : di === null ? "the entry itself" : nodeBtn(di));
      const go = (g, nodeId, text, cls = "wgran") => g ? ` <a class="${cls}" href="#/wasm-func/${encodeURIComponent(s.slug)}/${idx}/@${g[0]}${nodeId ? "/" + nodeId : ""}">${esc(text)}</a>` : "";
      const oc = outcomesOf(id), oi = O.filter((o) => o.handler === id);
      const outcomeLines = (oc.length ? `<div>outcomes: <span class="woutc">${oc.map((o) => esc(o.effect) + (isNode(o.handler) ? " → " + nodeBtn(o.handler) : o.handler ? " → " + esc(o.handler) : "") +
          (o.member != null ? ` <span class="muted">(in${go(blockGraph, "b" + o.member, "b" + o.member, "wmember")})</span>` : "")).join(", ")}</span>` +
          ' <span class="muted">(from the data; not edges, in no dominator basis)</span></div>' : "") +
        (oi.length ? `<div>handler for: ${oi.map((o) => nodeBtn(o.src) + " " + esc(o.effect)).join(", ")}</div>` : "");
      if (isNode(id) && instrG) {
        const k = Number(id.slice(1)), [bi, at] = cfg.nodes[k], b = cfg.blocks[bi];
        const lines = b.instrs.concat(b.term ? [b.term] : []);
        x += `<b>${id}</b> · <code>${esc(instrAt(k))}</code> <span class="muted">instruction ${at} of block b${bi}${cfg.entry === k ? " · entry" : ""}</span></p>` +
          `<pre class="code">${lines.map((l, j) => (j === at ? "▶ " : "  ") + esc(l)).join("\n") || "(empty)"}</pre>` +
          `<div>successors: ${edgeList(outs, "tgt")}</div><div>predecessors: ${edgeList(ins, "src")}</div>` + outcomeLines +
          `<div>${domLine} ${provBadge("browser")}</div>` +
          `<div class="muted">Typing is recorded per block${go(blockGraph, "b" + bi, "(block b" + bi + " at block level)")}.</div>`;
      } else if (isNode(id)) {
        const i = Number(id.slice(1)), b = cfg.blocks[i], fo = outs.filter((e) => !e.may), mo = outs.filter((e) => e.may);
        x += `<b>b${i}</b> · ${esc(instrN(b))} → <code>${esc(b.term || "falls through")}</code>` +
          ` <span class="muted">${b.path != null ? `at path [${esc(b.path)}] position ${esc(b.pos)}` : ""}${cfg.entry === i ? " · entry" : ""}</span></p>` +
          `<pre class="code">${esc(b.instrs.concat(b.term ? [b.term] : []).join("\n") || "(empty)")}</pre>` +
          `<div>flow successors: ${edgeList(fo, "tgt")}</div>` +
          `<div>flow predecessors: ${edgeList(ins.filter((e) => !e.may), "src")}</div>` +
          (!legacy && !mo.length ? "" : `<div>may-edges: ${mo.length ? edgeList(mo, "tgt") + ` <span class="muted">(conservative, from the marks ${esc(b.effects.join(", "))})</span>`
            : `<span class="muted">none${b.effects.length ? " (marks: " + esc(b.effects.join(", ")) + ")" : "; not a proof that this block cannot trap"}</span>`}</div>`) +
          outcomeLines + `<div>${domLine} ${provBadge("browser")}</div>` +
          (cfg.members && Array.isArray(cfg.members[i]) ? `<div>contains blocks ${cfg.members[i].map((k) => go(blockGraph, "b" + k, "b" + k, "wmember")).join(" ")}` +
            ` <span class="muted">(of ${esc(blockGraph ? blockGraph[0] : "the top-level numbering")}, as the data's <code>members</code> says)</span></div>` : "") +
          (containerOf(i) >= 0 ? `<div>part of ${go(memberGraph, "b" + containerOf(i), "block b" + containerOf(i), "wcontainer")} <span class="muted">of ${esc(memberGraph[0])}</span></div>` : "") +
          (instrGraph && (sameBlocks(V) || cfg.members) ? `<div>${go(instrGraph, (() => { const first = cfg.members ? (cfg.members[i] || [])[0] : i; const j = instrGraph[1].nodes.findIndex((nd) => nd[0] === first); return j < 0 ? "" : "n" + j; })(), "Expand: this block one node per instruction")}` +
            ` <span class="muted">(${esc(instrGraph[0])})</span></div>` : "") +
          (b.refs && Object.keys(b.refs).length ? "<div>references (syntactic, this block's own instructions): " +
            Object.entries(b.refs).map(([sp, xs]) => `${esc(sp)} ${xs.map((r) => sp === "func" && m.functions[r] && !m.functions[r].imported
              ? flink(s.slug, r, String(r)) : esc(r)).join(", ")}`).join("; ") + "</div>" : "") +
          (b.typing ? `<div>typing: <code>${esc(b.typing.in)} → ${esc(b.typing.out)}</code>` +
            (b.typing.inits.length ? ` initialising locals ${b.typing.inits.map(esc).join(", ")}` : "") +
            ` under labels <code>${esc(b.typing.labels || "(none)")}</code> <span class="muted">(this block's operand frame; local types and labels are the static context)</span>` +
            (b.typing.branch ? `<br>branch targets: <code>${esc(b.typing.branch)}</code>` : "") +
            "<br>" + runBadge("Cfg.bodyIfaces; each interface it records is an Instrs_ok derivation (bodyIfaces_typed) of this block's own instructions (bodyIfaces_lookup); for a validated body every block has one (bodyIfaces_complete)") +
            ' <span class="muted">A typing fact, not a statement about runs.</span></div>'
            : Array.isArray(b.memberTyping) && cfg.members && cfg.members[i] ? `<div class="wmtyping">typing, per member block: ` +
              b.memberTyping.map((ty, j) => `<br>${go(blockGraph, "b" + cfg.members[i][j], "b" + cfg.members[i][j], "wmember")}: ` + (ty
                ? `<code>${esc(ty.in)} → ${esc(ty.out)}</code> under labels <code>${esc(ty.labels || "(none)")}</code>`
                : '<span class="muted">no proved interface recorded</span>')).join("") +
              "<br>" + runBadge("Cfg.bodyIfaces per member; each is an Instrs_ok derivation (bodyIfaces_typed) of that member's own instructions") +
              ' <span class="muted">No interface is composed for the merged block: entering a structured instruction between members changes the label context, ' +
              "so the members' instructions are not one instruction sequence.</span></div>"
            : '<div class="muted">typing: no proved interface recorded for this block</div>');
      } else {
        const fi = ins.filter((e) => !e.may), mi = ins.filter((e) => e.may);
        x += `<b>${esc(id)}</b> <span class="muted">${esc({ exit: "the function returns", trap: "execution traps", raise: "an exception leaves the instruction (its handler is not resolved)",
          invalid: "a branch to a label that does not exist" }[id] || "")}</span></p>` +
          `<div>control (flow) edges in: <b>${fi.length}</b> ${edgeList(fi, "src")}</div>` +
          (id === "exit" ? "" : `<div>may-edges in: <b>${mi.length}</b> ${edgeList(mi, "src")}` +
            (mi.length ? ' <span class="muted">(drawn while this node is selected)</span>' : "") + "</div>") +
          `<div>${domLine} ${provBadge("browser")}</div>`;
      }
      side.innerHTML = x;
    };
    // Select a node: inspector, highlight, its may-edges, the address bar; keeps the layout.
    const select = (id, center) => {
      sel = id && domNodes.includes(id) && (view !== "flat" || wcy.getElementById(id).length) ? id : null;
      $("#wgo").value = sel || "";
      history.replaceState(null, "", permalink(sel));
      if (!sel) { $("#wside").classList.add("muted"); $("#wside").innerHTML = "Click a node (or pick one above) for its instructions, edges and typing."; }
      else inspect(sel);
      const cid = view === "flat" ? sel : sel && "d:" + sel;
      wcy.batch(() => { wcy.nodes(".sel").removeClass("sel"); wcy.edges(".hl").removeClass("hl");
        if (cid) { const n = wcy.getElementById(cid); n.addClass("sel"); n.connectedEdges().addClass("hl"); } });
      applyMay();
      if (center && cid) {
        const n = wcy.getElementById(cid);
        if (n.length) {
          const bb = n.renderedBoundingBox(), w = wcy.width(), hgt = wcy.height();
          if (wcy.zoom() < 0.5) wcy.zoom(0.85);
          if (bb.x1 < 0 || bb.y1 < 0 || bb.x2 > w || bb.y2 > hgt || wcy.zoom() === 0.85) wcy.center(n);
        }
      }
    };
    const wireNodes = () => {
      wcy.on("tap", "node", (ev) => { if (ev.target.data("kind") === "group") return; select(view === "flat" ? ev.target.id() : ev.target.id().slice(2), false); });
      wcy.on("tap", (ev) => { if (ev.target === wcy) select(null); });
      wcy.on("mouseover", "node", (ev) => { if (view !== "flat") return; hov = ev.target.id(); ev.target.addClass("hov"); applyMay(); });
      wcy.on("mouseout", "node", (ev) => { if (view !== "flat") return; hov = null; ev.target.removeClass("hov"); applyMay(); });
    };
    const flat = () => {
      if (wcy) wcy.destroy();
      view = "flat";
      $("#wflat").setAttribute("aria-pressed", "true"); $("#wdom").setAttribute("aria-pressed", "false");
      // Instruction-level graphs keep block boundaries: each block is a box around its instructions.
      const els = instrG ? [...new Set(cfg.nodes.map((nd) => nd[0]))].map((bi) => ({ data: { id: "g" + bi, label: "b" + bi, kind: "group" } })) : [];
      nodeIds.forEach((id, k) => els.push({ data: { id, label: nodeLabel(id), kind: "block", entry: cfg.entry === k ? 1 : 0,
        marked: (!instrG && cfg.blocks[k].effects.length) || outcomesOf(id).length ? 1 : 0, ...(instrG ? { parent: "g" + cfg.nodes[k][0] } : {}) } }));
      for (const t of specials) els.push({ data: { id: t, label: specialLabel(t), kind: t === "exit" ? "exit" : "special", entry: cfg.entry === t ? 1 : 0 } });
      for (const e of E) {
        const back = isNode(e.tgt) && Number(e.tgt.slice(1)) <= e.a ? 1 : 0;
        els.push({ data: { id: "e" + e.i, source: e.src, target: e.tgt, kind: e.kind, back, special: !e.may && !isNode(e.tgt) && e.tgt !== "exit" ? 1 : 0 },
          classes: e.may ? "may" : "" });
      }
      // Handler links of outcomes: drawn like may-edges (on selection, hover or request), never laid out.
      for (const o of O) if (isNode(o.handler)) els.push({ data: { id: "o" + o.i, source: o.src, target: o.handler, kind: "outcome" }, classes: "may outc" });
      wcy = cytoscape({ container: $("#wcy"), elements: els, minZoom: 0.05, maxZoom: 3, wheelSensitivity: 0.25, style: graphStyle(WCFG_STYLE),
        layout: { name: "preset" } });
      // Lay out on the flow edges only, once: drawing or hiding may-edges never moves a node. Nodes
      // reached only by may-edges (typically raise, often trap) go below the graph as sinks.
      if (flatPos) wcy.nodes().forEach((n) => { if (flatPos[n.id()]) n.position(flatPos[n.id()]); });
      else {
        const sinks = wcy.nodes().filter((n) => n.data("kind") === "special" && !flowE.some((e) => e.tgt === n.id()));
        wcy.elements().not(".may").not(sinks).layout({ name: "dagre", rankDir: "TB", nodeSep: 30, rankSep: 42, edgeSep: 12, animate: false, fit: false }).run();
        const bb = wcy.elements().not(".may").not(sinks).boundingBox();
        sinks.forEach((n, k) => n.position({ x: bb.x1 + bb.w / 2 + (k - (sinks.length - 1) / 2) * 140, y: bb.y2 + 70 }));
        flatPos = {}; wcy.nodes().forEach((n) => { flatPos[n.id()] = Object.assign({}, n.position()); });
      }
      wcy.fit(undefined, 30);
      $("#wprov").innerHTML = "";
      wireNodes();
      wireZoom(typeof cfg.entry === "number" ? nid(cfg.entry) : null, true);
      if (sel) select(sel, true); else applyMay();
    };
    const dom = () => {
      if (wcy) wcy.destroy();
      view = "dom";
      $("#wflat").setAttribute("aria-pressed", "false"); $("#wdom").setAttribute("aria-pressed", "true");
      const basis = $("#wbasis").value, r = DOM[basis], kt = KT[basis];
      wcy = drawDomTree($("#wcy"), domNodes, r.idom, labelOf, { "font-size": 12, "text-wrap": "wrap", height: "label" });
      wcy.style().selector("node.sel").style({ "underlay-color": "#f2c94c", "underlay-opacity": 0.7, "underlay-padding": 6 }).update();
      const unreach = domNodes.filter((n) => !r.idom.has(n));
      const inB = basisEdges(basis).length, outB = E.length - inB;
      const diffs = BASES.filter((o) => o.id !== basis).map((o) => {
        const d = domNodes.filter((n) => DOM[o.id].idom.get(n) !== r.idom.get(n));
        return d.length ? `on ${esc(basisText(o.id))} the immediate dominator differs for ` + d.map((n) => `${esc(n)} (${esc(domName(DOM[o.id].idom.get(n)))})`).join(", ")
          : `${esc(basisText(o.id))} gives the same tree`; });
      $("#wprov").innerHTML = provBadge("browser") + ` <span class="muted" id="wdomnote">${esc(vlabel)}: immediate dominators from ${esc(domEntry)} over ` +
        `the ${inB} edges of basis “${esc(basisText(basis))}” (kinds ${esc(basisOf(basis).kinds.join(", "))})` +
        (outB ? `; the other ${outB} edges are not in this basis` : "") +
        (basisOf(basis).relation ? `; intended relation <code>${esc(basisOf(basis).relation)}</code> (metadata, not checked here)` : "") +
        (kt ? `; the Lean kernel-checked table of ${link("machine", kt.name)} ` +
          (kt.same ? `is the same graph (nodes, entry, edges) and the same tree, compared here node by node ${provBadge("lean", kt.thm)}` : `<b>is not shown as evidence</b>: it ${esc(kt.why)}`) : "") +
        `. ${diffs.length ? diffs.join("; ") + ". " : ""}` +
        `A fact about the graph as drawn, not about execution.${unreach.length ? " Not reached on this basis: " + esc(unreach.join(", ")) : ""}</span>`;
      wireNodes();
      wireZoom(domEntry ? "d:" + domEntry : null, true);
      if (sel) select(sel, true);
    };
    wireZoomButtons();
    $("#wflat").addEventListener("click", flat);
    $("#wdom").addEventListener("click", dom);
    $("#weff").addEventListener("change", applyMay);
    $("#wbasis").addEventListener("change", () => { if (view === "dom") dom(); else if (sel) inspect(sel); });
    if ($("#wvariant")) $("#wvariant").addEventListener("change", (ev) => {
      location.hash = `#/wasm-func/${encodeURIComponent(s.slug)}/${idx}/@${ev.target.value}${sel ? "/" + sel : ""}`; });
    $("#wgo").addEventListener("change", (ev) => select(ev.target.value || null, true));
    $("#wside").addEventListener("click", (ev) => { const b = ev.target.closest("button.wnode"); if (b) select(b.dataset.n, true); });
    const order = nodeIds.concat(specials);
    $("#wcy").addEventListener("keydown", (ev) => {
      if (ev.altKey || ev.ctrlKey || ev.metaKey) return;
      const k = ev.key, at = order.indexOf(sel);
      const z = (f) => wcy.zoom({ level: wcy.zoom() * f, renderedPosition: { x: wcy.width() / 2, y: wcy.height() / 2 } });
      const step = (es, end) => { const e = es.find((x) => !x.may) || es[0]; if (e) select(e[end], true); };
      if (k === "j" || k === "ArrowRight") select(order[(at + 1) % order.length], true);
      else if (k === "k" || k === "ArrowLeft") select(order[at <= 0 ? order.length - 1 : at - 1], true);
      else if (k === "ArrowDown") { if (sel) step(outOf.get(sel) || [], "tgt"); else select(order[0], true); }
      else if (k === "ArrowUp") { if (sel) step(into.get(sel) || [], "src"); else select(order[0], true); }
      else if (k === "e") { $("#weff").checked = !$("#weff").checked; applyMay(); }
      else if (k === "+" || k === "=") z(1.3);
      else if (k === "-") z(1 / 1.3);
      else if (k === "0") wcy.fit(undefined, 30);
      else if (k === "Escape") select(null);
      else return;
      ev.preventDefault();
    });
    flat();
    if (sel) $("#wcfg").scrollIntoView();
  };
  return { html: h, init, dispose: disposeWcy };
}
// The block CFG's own marks, on top of graphStyle: marked blocks get a warm fill; may-edges are
// hidden unless shown (class "show"); control edges into trap/raise are solid and dark red.
const WCFG_STYLE = [
  { selector: "node[kind = 'block']", style: { "font-size": 13 } },
  { selector: "node[marked = 1]", style: { "background-color": "#fff4ef" } },
  { selector: "node[kind = 'special']", style: { "background-color": "#fdecec", "font-size": 11 } },
  { selector: "edge.may", style: { display: "none", width: 1.1, "line-opacity": 0.75, "arrow-scale": 0.8 } },
  { selector: "edge.may.show", style: { display: "element" } },
  { selector: "edge[special = 1]", style: { "line-color": "#b42318", "target-arrow-color": "#b42318", width: 2.5 } },
  { selector: "node.hov", style: { "underlay-color": "#2f5d9e", "underlay-opacity": 0.18, "underlay-padding": 5 } },
  { selector: "node.sel", style: { "underlay-color": "#f2c94c", "underlay-opacity": 0.7, "underlay-padding": 6 } },
  { selector: "edge.hl", style: { width: 2.6, "z-index": 10 } },
  { selector: "edge.may.hl", style: { width: 1.8 } },
  { selector: "edge.outc", style: { "line-color": "#7c3aed", "target-arrow-color": "#7c3aed", "line-style": "dashed", "line-dash-pattern": [2, 2] } },
  { selector: "node[kind = 'group']", style: { shape: "round-rectangle", "background-color": "#f5f7fa", "background-opacity": 0.6, "border-color": "#9aa0a6",
    "border-width": 1, "border-style": "dashed", label: "data(label)", "text-valign": "top", "text-halign": "left", "font-size": 12, color: "#4b5563", padding: 10 } }];

// ---------- SQL: query, schema, about ----------

registerView({ id: "wasm", title: "Wasm", nav: 80, render: wasmPage });
registerView({ id: "wasm-component", title: "Wasm component", tab: "wasm", render: wasmComponentPage });
registerView({ id: "wasm-module", title: "Wasm module", tab: "wasm", render: wasmModulePage });
registerView({ id: "wasm-func", title: "Wasm function", tab: "wasm", render: wasmFuncPage });
