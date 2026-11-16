const COLORS = { holds: "#2e9d4f", fails: "#d64545", unknown: "#9aa0a6" };
const GROUP_LOOKUPS = 500;
function shortName(n) {
  const sep = n.includes("/") ? "/" : ".", p = n.split(sep);
  return p.length > 2 ? "…" + sep + p.slice(-2).join(sep) : n;
}
async function graph(focus) {
  const local = (await tq("projects", "SELECT root FROM projects WHERE origin = 'local' LIMIT 1"))[0];
  const root = (local && local.root) || "";
  focus = focus || root || ((await q("SELECT name FROM problems ORDER BY name LIMIT 1"))[0] || {}).name || "";
  const html = `<div class="controls">
    <label>focus <input type="text" id="gfocus" list="gnames" size="44" value="${esc(focus)}"></label>
    <datalist id="gnames"></datalist>
    <label>depth <input type="number" id="gdepth" min="1" max="999" value="99" style="width:4em"></label>
    <label>max nodes <input type="number" id="gmax" min="10" max="5000" value="300" style="width:5em"></label>
    <label><input type="checkbox" id="gdet"> detached problems</label>
    <button id="gdraw">Draw</button> <button id="gfit">Fit</button>
    <span class="legend"><span>${badge("holds")}</span><span>${badge("fails")}</span><span>${badge("unknown")}</span>
    <span class="muted">box = group (holds/fails/unknown children) · dashed edge = refutation route · dotted = instance · thick edge = proved · thick border = root · dashed border = detached</span></span>
    <span id="gcount" class="muted"></span></div>
    <div id="graphwrap"><div id="cy"></div><div id="side"><p class="muted">Click a node for its details; double-click to refocus.</p></div></div>`;
  const init = async () => {
    const draw = () => drawGraph($("#gfocus").value.trim(), +$("#gdepth").value || 99, +$("#gmax").value || 300, $("#gdet").checked, root)
      .catch((e) => { $("#gcount").innerHTML = `<span class="err">${esc(e.message || e)}</span>`; }).then(updateStats);
    $("#gdraw").addEventListener("click", draw);
    $("#gfocus").addEventListener("keydown", (e) => { if (e.key === "Enter") draw(); });
    $("#gfit").addEventListener("click", () => cy && cy.fit(undefined, 20));
    // Suggestions: the first 30 problem names containing the text (read from the name index).
    let timer = null;
    $("#gfocus").addEventListener("input", () => {
      clearTimeout(timer);
      timer = setTimeout(async () => {
        const t = $("#gfocus").value.trim();
        if (t.length < 2) return;
        const rows = await q("SELECT name FROM problems WHERE instr(name, ?) > 0 ORDER BY name LIMIT 30", [t]);
        $("#gnames").innerHTML = rows.map((r) => `<option value="${esc(r.name)}">`).join("");
        updateStats();
      }, 300);
    });
    await draw();
  };
  return { html, init, dispose: () => { if (cy) { cy.destroy(); cy = null; } } };
}
// Nodes: the focus's parents (up to 50), then whole levels below the focus, down to `depth` levels
// and while the total stays within `maxNodes` (dagre is slow on thousands of nodes). Each level is
// one bounded query for the edges out of the previous level.
async function drawGraph(focus, depth, maxNodes, withDetached, root) {
  const exists = async (n) => n && (await q("SELECT 1 AS x FROM problems WHERE name = ?", [n])).length > 0;
  let note = "";
  if (!(await exists(focus))) { if (focus) note = ` · no problem ${focus}`; focus = root; }
  const keep = new Set(), out = new Map();
  // The edges out of `names`, at most `cap` rows in all. Rows come in parent order, so when the
  // cap cuts a read every parent before the cut is complete; `out` records only complete ones.
  // Returns whether every parent was read.
  const cap = 4 * maxNodes;
  const fetchOut = async (names) => {
    const todo = names.filter((n) => !out.has(n)).sort();
    let budget = cap;
    for (let i = 0; i < todo.length; i += 300) {
      const part = todo.slice(i, i + 300);
      const rows = await q(`SELECT parent, child, kind, via FROM edges WHERE parent IN (${ph(part.length)}) ORDER BY parent LIMIT ${budget + 1}`, part);
      const cut = rows.length > budget ? rows[budget].parent : null;
      for (const n of part) if (cut === null || n < cut) out.set(n, []);
      for (const e of rows) if (out.has(e.parent) && e.parent !== cut) out.get(e.parent).push(e);
      if (cut !== null) return false;
      budget -= rows.length;
    }
    return true;
  };
  if (await exists(focus)) {
    const parents = await q("SELECT DISTINCT parent FROM edges WHERE child = ? LIMIT 50", [focus]);
    for (const r of parents) keep.add(r.parent);
    keep.add(focus);
    let frontier = [focus];
    for (let d = 0; d < depth && frontier.length; d++) {
      const complete = await fetchOut(frontier);
      const next = new Set();
      for (const n of frontier) for (const e of out.get(n) || []) if (!keep.has(e.child)) next.add(e.child);
      if (!complete) { note += ` · stopped at depth ${d} (the next level has more than ${cap} edges; raise max nodes or refocus)`; break; }
      if (next.size && keep.size + next.size > maxNodes) { note += ` · stopped at depth ${d} (next level has ${next.size} nodes; raise max nodes or refocus)`; break; }
      for (const n of next) keep.add(n);
      frontier = [...next];
    }
    await fetchOut([...keep]);
  }
  if (withDetached && keep.size < maxNodes) {
    for (const r of await q("SELECT name FROM problems WHERE detached = 1 ORDER BY name LIMIT ?", [maxNodes - keep.size])) keep.add(r.name);
    await fetchOut([...keep]);
  }
  // Node data from indexes where possible: group-ness from objects(kind, name), detached-ness,
  // verdicts by problem; titles only for groups.
  const names = [...keep];
  const groupSet = new Set((await inChunks("SELECT name FROM objects WHERE kind = 'group' AND name IN ($)", names)).map((r) => r.name));
  const detached = new Set((await inChunks("SELECT name FROM problems WHERE detached = 1 AND name IN ($)", names)).map((r) => r.name));
  const titles = new Map((await inChunks("SELECT name, title FROM problems WHERE name IN ($)", [...groupSet])).map((r) => [r.name, r.title]));
  const checked = new Set();
  const lookUp = async (ns) => {
    for (const n of ns) checked.add(n);
    for (const r of await inChunks("SELECT problem, summary, verdict FROM summary WHERE problem IN ($)", ns)) { verdictOf.set(r.problem, r.verdict); summaryOf.set(r.problem, r.summary); }
  };
  await lookUp(names);
  // A group's label tallies its children's verdicts; at most GROUP_LOOKUPS children that are not
  // drawn are looked up, the rest are counted as unchecked.
  const hiddenChildren = [...new Set([...groupSet].flatMap((g) => (out.get(g) || []).map((e) => e.child)).filter((c) => !checked.has(c)))];
  await lookUp(hiddenChildren.slice(0, GROUP_LOOKUPS));
  const gv = new Map();
  for (const g of groupSet) {
    const c = { holds: 0, fails: 0, unknown: 0, unchecked: 0 };
    for (const e of out.get(g) || []) c[checked.has(e.child) ? verdictOf.get(e.child) || "unknown" : "unchecked"]++;
    gv.set(g, c);
  }
  const els = [];
  for (const n of keep) {
    const isGroup = groupSet.has(n);
    let label = shortName(n);
    if (isGroup) {
      const c = gv.get(n);
      label = (titles.get(n) || shortName(n)) + (out.has(n) ? `\n${c.holds} / ${c.fails} / ${c.unknown}` + (c.unchecked ? ` (${c.unchecked} unchecked)` : "") : "");
    } else if (summaryOf.has(n)) label += "\n" + summaryOf.get(n);
    const hidden = (out.get(n) || []).filter((e) => !keep.has(e.child)).length;
    if (hidden) label += ` (+${hidden} hidden)`;
    else if (!out.has(n)) label += " (+ more, not read)";
    els.push({ data: { id: n, label, verdict: verdictOf.get(n) || "unknown", group: isGroup ? 1 : 0, detached: detached.has(n) ? 1 : 0, root: n === root ? 1 : 0, focus: n === focus ? 1 : 0 } });
  }
  let i = 0;
  for (const n of keep) for (const e of out.get(n) || []) if (keep.has(e.child)) els.push({ data: { id: "e" + (i++), source: e.parent, target: e.child, kind: e.kind, via: e.via || "" } });
  $("#gcount").textContent = `${keep.size} problems, ${i} edges${note}`;
  if (cy) cy.destroy();
  cy = cytoscape({
    container: $("#cy"), elements: els, minZoom: 0.05,
    style: [
      { selector: "node", style: { label: "data(label)", "text-wrap": "wrap", "text-overflow-wrap": "anywhere", "text-max-width": 140, "font-size": 10, "text-valign": "center", "text-halign": "center",
        width: 150, height: 34, shape: "round-rectangle", "background-color": (n) => COLORS[n.data("verdict")], color: "#fff", "text-outline-width": 0,
        "border-width": 1, "border-color": "#33393f" } },
      { selector: "node[group = 1]", style: { shape: "rectangle", "background-color": "#f4f6f8", color: "#1d2329", width: 180, height: 44, "border-width": 2, "border-color": "#2f5d9e", "font-weight": 600 } },
      { selector: "node[detached = 1]", style: { "border-style": "dashed", opacity: 0.75 } },
      { selector: "node[root = 1]", style: { "border-width": 4, "border-color": "#111" } },
      { selector: "node[focus = 1]", style: { "underlay-color": "#f2c94c", "underlay-opacity": 0.6, "underlay-padding": 6 } },
      { selector: "node:selected", style: { "overlay-color": "#2f5d9e", "overlay-opacity": 0.25 } },
      { selector: "edge", style: { width: 1.4, "curve-style": "bezier", "target-arrow-shape": "triangle", "arrow-scale": 0.8, "line-color": "#8a939c", "target-arrow-color": "#8a939c" } },
      { selector: "edge[kind = 'refute']", style: { "line-style": "dashed", "line-color": "#c46a6a", "target-arrow-color": "#c46a6a" } },
      { selector: "edge[kind = 'instance']", style: { "line-style": "dotted", "line-color": "#5b7fb5", "target-arrow-color": "#5b7fb5" } },
      { selector: "edge[via != '']", style: { width: 2.2 } },
    ],
    layout: { name: "dagre", rankDir: "TB", nodeSep: 20, rankSep: 50, animate: false },
  });
  const side = async (h) => { const html = await h; $("#side").innerHTML = html; updateStats(); };
  cy.on("tap", "node", (e) => side(problemDetail(e.target.id())));
  cy.on("dbltap", "node", (e) => { location.hash = href("graph", e.target.id()); });
  cy.on("tap", "edge", (e) => { const d = e.target.data();
    side(dl({ parent: d.source, child: d.target, kind: d.kind, via: d.via || null }).then((x) => "<h2>Edge</h2>" + x)); });
  // A wide level makes "fit" unreadable: then zoom in on the focus instead.
  if (cy.zoom() < 0.5 && cy.getElementById(focus).length) { cy.zoom(0.8); cy.center(cy.getElementById(focus)); }
  if (focus && cy.getElementById(focus).length) await side(problemDetail(focus));
}

registerView({ id: "graph", title: "Graph", nav: 20, render: graph });
