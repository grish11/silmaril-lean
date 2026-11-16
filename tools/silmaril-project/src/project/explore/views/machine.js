let mcy = null;
async function machinePage(name) {
  const m = (await q("SELECT * FROM machines WHERE name = ?", [name]))[0];
  if (!m) return `<p class="err">no machine ${esc(name)}</p>`;
  let doc;
  try { doc = JSON.parse(m.canonical); } catch (e) { return `<p class="err">machine ${esc(name)}: canonical JSON does not parse</p>`; }
  const ly = doc.layers || {};
  const has = (k, s) => (ly[k] || []).includes(s);
  let h = `<h2>Machine <code>${esc(name)}</code></h2>`;
  if (m.doc) h += `<p>${esc(m.doc)}</p>`;
  h += `<p class="legend muted"><span>${doc.states.length} states</span><span>${doc.labels.length} labels</span><span>${doc.edges.length} edges</span>` +
    `<span>deterministic: ${m.deterministic ? "yes" : "no"}</span> — initial: thick border; accepting: double border; rejecting: orange; error: red; ` +
    "↺ n: n self-loops. Click a state or an edge for its transitions.</p>";
  const big = doc.states.length > 12 || doc.edges.length > 40;
  h += '<div class="controls"><button id="vflat">Flat graph</button><button id="vdom">Dominator tree</button>' +
    '<button id="mfit">fit</button> <span class="muted">scroll to zoom, drag to pan</span> <span id="mprov"></span></div>';
  h += `<div id="mcy" style="height:${big ? 78 : 62}vh;min-height:420px;border:1px solid var(--line);background:var(--panel)"></div>`;
  h += '<div id="mdetail" class="muted" style="margin:8px 0;min-height:1.5em">Click a state or an edge.</div>';
  h += "<h2>Bindings (typed machines proved equal to this document)</h2>" + await tableOf(await first(DETAIL,
    "SELECT name, decl, marks, theorem, module FROM machine_bindings WHERE machine = ? ORDER BY name", [name]), null, { hints: { name: "" } });
  h += "<h2>Record</h2>" + await dl(Object.fromEntries(Object.entries(m).filter(([k]) => k !== "canonical")), { name: "" });
  h += "<h2>Canonical JSON</h2><textarea readonly>" + esc(m.canonical) + "</textarea>";
  const init = async () => {
    if (typeof cytoscape === "undefined") { $("#mcy").innerHTML = '<p class="err">cytoscape did not load</p>'; return; }
    const merged = new Map(), loops = new Map();
    for (const [a, l, b] of doc.edges) {
      if (a === b) { if (!loops.has(a)) loops.set(a, []); loops.get(a).push(l); continue; }
      const k = a + "\u0000" + b;
      if (!merged.has(k)) merged.set(k, { source: a, target: b, labels: [] });
      merged.get(k).labels.push(l);
    }
    const els = doc.states.map((s) => {
      const n = (loops.get(s) || []).length;
      return { data: { id: "s:" + s, name: s, label: n ? `${s}\n↺ ${n}` : s,
        color: has("error", s) ? "#d64545" : has("rejecting", s) ? "#e8963a" : has("accepting", s) ? "#2e9d4f" : "#2f5d9e",
        bw: has("initial", s) ? 4 : 1.5, bs: has("accepting", s) ? "double" : "solid" } };
    });
    let i = 0;
    for (const e of merged.values()) {
      const c = compactLabels(e.labels);
      els.push({ data: { id: "e" + (i++), source: "s:" + e.source, target: "s:" + e.target, all: e.labels,
        label: c.length > 3 ? `${c.slice(0, 3).join("\n")}\n+${c.length - 3} more` : c.join("\n") } });
    }
    mcy = cytoscape({ container: $("#mcy"), elements: els, wheelSensitivity: 0.2,
      layout: big ? { name: "dagre", rankDir: "LR", nodeSep: 70, rankSep: 220, edgeSep: 30 }
        : { name: "dagre", rankDir: "LR", nodeSep: 40, rankSep: 90 },
      style: [
        { selector: "node", style: { label: "data(label)", "background-color": "#fff", "border-color": "data(color)", "border-width": "data(bw)",
          "border-style": "data(bs)", color: "#1d2329", "font-size": big ? 12 : 11, "text-valign": "center", "text-halign": "center", shape: "round-rectangle",
          "text-wrap": "wrap", width: "label", height: big ? "label" : 26, padding: big ? 10 : 8 } },
        { selector: "edge", style: { label: "data(label)", "curve-style": "bezier", "target-arrow-shape": "triangle", width: 1.2,
          "line-color": "#9aa0a6", "target-arrow-color": "#9aa0a6", "font-size": big ? 9 : 9, "text-wrap": "wrap",
          "text-background-color": "#fbfbfa", "text-background-opacity": big ? 0.9 : 0.85, "text-background-padding": big ? 2 : 0,
          "text-rotation": big ? "autorotate" : "none", "control-point-step-size": big ? 60 : 40 } },
        { selector: ":selected", style: { "line-color": "#2f5d9e", "target-arrow-color": "#2f5d9e", "border-color": "#2f5d9e" } }] });
    // A wide graph fitted to the box is unreadable: start at a readable zoom on the initial state.
    if (mcy.zoom() < 0.5) {
      const n = mcy.getElementById("s:" + ((ly.initial || [])[0] || doc.states[0]));
      mcy.zoom(0.8);
      if (n.length) { const p = n.position(); mcy.pan({ x: 40 - p.x * 0.8 + n.width() * 0.4, y: mcy.height() / 2 - p.y * 0.8 }); } else mcy.center();
    }
    const show = (html) => { $("#mdetail").classList.remove("muted"); $("#mdetail").innerHTML = html; };
    // The dominator view: the kernel-checked table when the registry has one (one initial
    // state), otherwise computed here from the initial states (several: a synthetic root).
    const domView = () => {
      mcy.destroy();
      let idom, prov;
      if (m.dominators) {
        const t = JSON.parse(m.dominators);
        idom = new Map(Object.entries(t));
        prov = provBadge("lean", m.dominator_theorem) + ` <span class="muted">immediate dominators of this document's graph, from ${esc((ly.initial || [])[0])}; ` +
          "the exact dominator tree is unique on reachable states (<code>Graph.exact_unique</code>). " +
          "This is a fact about the graph as drawn, not about any execution it may describe.</span>";
        // unreachable states have no dominator: null in the table; keep reachable ones only
        const reach = dominators(doc.states, doc.edges.map(([a, , b]) => [a, b]), ly.initial || []).reachable;
        for (const s of [...idom.keys()]) if (!reach.has(s)) idom.delete(s);
      } else {
        const roots = (ly.initial || []).length ? ly.initial : [doc.states[0]];
        const r = dominators(doc.states, doc.edges.map(([a, , b]) => [a, b]), roots);
        idom = r.idom;
        prov = provBadge("browser") + ` <span class="muted">from ${r.synthetic ? "a synthetic root over " : ""}${esc(roots.join(", "))}` +
          `${(ly.initial || []).length ? "" : " (no initial state: the first state)"}</span>`;
      }
      const unreach = doc.states.filter((s) => !idom.has(s));
      $("#mprov").innerHTML = prov + (unreach.length ? ` <span class="muted">unreachable: ${esc(unreach.join(", "))}</span>` : "");
      mcy = drawDomTree($("#mcy"), doc.states, idom, (s) => s);
    };
    $("#vdom").addEventListener("click", domView);
    $("#mfit").addEventListener("click", () => mcy && mcy.fit(undefined, 30));
    $("#vflat").addEventListener("click", () => { route(); });
    $("#mprov").innerHTML = '<span class="muted">flat graph of the document</span>';
    const list = (ls) => "<ul style=\"margin:4px 0\">" + ls.map((l) => `<li><code>${esc(l)}</code></li>`).join("") + "</ul>";
    mcy.on("tap", "edge", (ev) => {
      const d = ev.target.data();
      show(`<b>${esc(d.source.slice(2))} → ${esc(d.target.slice(2))}</b> (${d.all.length} labels)` + list(d.all));
    });
    mcy.on("tap", "node", (ev) => {
      const s = ev.target.data("name");
      const out = doc.edges.filter(([a, , b]) => a === s && b !== s).map(([, l, b]) => `${l} → ${b}`);
      show(`<b>${esc(s)}</b>` + ((loops.get(s) || []).length ? `<br>self-loops: ${list(loops.get(s))}` : "") +
        (out.length ? `outgoing: ${list(out)}` : "<br>no outgoing transitions to other states"));
    });
  };
  return { html: h, init, dispose: () => { if (mcy) { mcy.destroy(); mcy = null; } } };
}

registerView({ id: "machine", title: "Machine", tab: "machines", render: machinePage });
