const GROUP_LOOKUPS = 500;
// By default the graph does not draw every problem: the leaves under one parent (children with no
// children of their own) are drawn as one node per status code ("12 × THM"), which keeps their
// count and status visible. Clicking such a node lists them; "expand" draws them one by one
// (per parent), and "every problem" draws all leaves everywhere. Problems that need attention (an
// unexplained failure, an unmet expectation), the focus and the root are always drawn alone.
let gExpanded = new Set(), gEvery = false;
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
    <label title="draw every leaf problem instead of one node per parent and status"><input type="checkbox" id="gevery"${gEvery ? " checked" : ""}> every problem</label>
    <button id="gdraw">Draw</button> <button id="gfit">Fit</button></div>
    <p class="legend muted">${statusBadge({ summary: "THM", verdict: "holds" })} status code ·
    <span class="st st-bad">CSA<b>!</b></span> unexplained failure · <span class="st st-unmet">OPN<b>?</b></span> unmet expectation ·
    blue box = group (holds/fails/unknown children) · stacked = leaves grouped by status (click: list, expand) · dashed edge = refutation route ·
    dotted = instance · thick edge = proved · thick border = root · dashed border = detached <span id="gcount"></span></p>
    <div id="graphwrap"><div id="cy"></div><div id="side"><p class="muted">Click a node for its details; double-click to refocus.</p></div></div>`;
  const init = async () => {
    const draw = () => !$("#gfocus") ? Promise.resolve() : drawGraph($("#gfocus").value.trim(), +$("#gdepth").value || 99, +$("#gmax").value || 300, $("#gdet").checked, root)
      .catch((e) => {
        if (e instanceof Superseded) return;
        if (e instanceof SourceChanged) { $("#main").innerHTML = changedNotice(e); wireChangedNotice($("#main")); return; }
        $("#gcount").innerHTML = `<span class="err">${esc(e.message || e)}</span>`;
      }).then(updateStats);
    $("#gdraw").addEventListener("click", draw);
    $("#gevery").addEventListener("change", (e) => { gEvery = e.target.checked; gExpanded = new Set(); draw(); });
    window.explore.redrawGraph = draw;
    $("#gfocus").addEventListener("keydown", (e) => { if (e.key === "Enter") draw(); });
    $("#gfit").addEventListener("click", () => cy && cy.fit(undefined, 20));
    // Suggestions: the first 30 problem names containing the text (read from the name index).
    let timer = null;
    $("#gfocus").addEventListener("input", () => {
      clearTimeout(timer);
      timer = setTimeout(async () => {
        if (!$("#gfocus")) return;
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
  // Statuses (with expectations and markings) of the drawn problems, and of up to GROUP_LOOKUPS
  // children of groups that are not drawn, for the groups' tallies; the rest are unchecked.
  const checked = new Set();
  const lookUp = async (ns) => {
    for (const n of ns) checked.add(n);
    await resolve(ns.map((n) => ({ problem: n })), ["problem"], HINTS, false);
  };
  await lookUp(names);
  const hiddenChildren = [...new Set([...groupSet].flatMap((g) => (out.get(g) || []).map((e) => e.child)).filter((c) => !checked.has(c)))];
  await lookUp(hiddenChildren.slice(0, GROUP_LOOKUPS));
  const gv = new Map();
  for (const g of groupSet) {
    const c = { holds: 0, fails: 0, unknown: 0, unchecked: 0 };
    for (const e of out.get(g) || []) c[checked.has(e.child) ? verdictOf.get(e.child) || "unknown" : "unchecked"]++;
    gv.set(g, c);
  }
  // Leaves grouped under their parent by status code. A leaf is a problem read to have no
  // children; it stays alone when it is the focus or the root, needs attention, or its parent is
  // expanded. A leaf with several parents is counted under each.
  const isLeaf = (n) => out.has(n) && out.get(n).length === 0 && !groupSet.has(n);
  const alone = (n) => n === focus || n === root || ["bad", "unmet"].includes((statusInfo(statusOf.get(n)) || {}).cls);
  const stacks = new Map();   // "parent\u0000code" -> { parent, code, kind, members }
  const stacked = new Set();
  if (!gEvery) for (const p of keep) {
    if (gExpanded.has(p)) continue;
    for (const e of out.get(p) || []) {
      const c = e.child;
      if (!keep.has(c) || !isLeaf(c) || alone(c)) continue;
      const code = (statusOf.get(c) || {}).summary || "none";
      const k = p + "\u0000" + code + "\u0000" + e.kind;
      if (!stacks.has(k)) stacks.set(k, { parent: p, code, kind: e.kind, members: [] });
      stacks.get(k).members.push(c);
    }
  }
  // a stack of one is just the problem
  for (const [k, st] of stacks) if (st.members.length < 2) stacks.delete(k);
  for (const st of stacks.values()) for (const m of st.members) stacked.add(m);
  // a stacked leaf is drawn alone too where another parent of it is expanded
  const underExpanded = new Set([...keep].filter((p) => gExpanded.has(p)).flatMap((p) => (out.get(p) || []).map((e) => e.child)));
  const drawnAlone = (n) => !stacked.has(n) || underExpanded.has(n);
  const els = [];
  const shown = [...keep].filter(drawnAlone);
  for (const n of shown) {
    const isGroup = groupSet.has(n);
    let label = shortName(n);
    if (isGroup) {
      const c = gv.get(n);
      label = (titles.get(n) || shortName(n)) + (out.has(n) ? `\n${c.holds} / ${c.fails} / ${c.unknown}` + (c.unchecked ? ` (${c.unchecked} unchecked)` : "") : "");
    } else {
      const i = statusInfo(statusOf.get(n));
      if (i) label += "\n" + i.code + (i.cls === "bad" ? " !" : i.cls === "unmet" ? " ?" : "");
    }
    const hidden = (out.get(n) || []).filter((e) => !keep.has(e.child)).length;
    if (hidden) label += ` (+${hidden} hidden)`;
    else if (!out.has(n)) label += " (+ more, not read)";
    const cls = (statusInfo(statusOf.get(n)) || {}).cls || "";
    els.push({ data: { id: n, label, att: cls, group: isGroup ? 1 : 0, detached: detached.has(n) ? 1 : 0, root: n === root ? 1 : 0, focus: n === focus ? 1 : 0 } });
  }
  const drawn = new Set(shown);
  let i = 0, nStacks = 0;
  for (const st of stacks.values()) {
    const id = "stack:" + (nStacks++);
    st.id = id;
    const loose = st.members.filter((m) => !drawn.has(m));
    if (!loose.length) continue;
    els.push({ data: { id, label: `${loose.length} × ${SZS_SHORT[st.code] || st.code}`, stack: 1, att: "", group: 0, detached: 0, root: 0, focus: 0 } });
    els.push({ data: { id: "e" + (i++), source: st.parent, target: id, kind: st.kind, via: "" } });
  }
  for (const n of shown) for (const e of out.get(n) || []) if (drawn.has(e.child)) els.push({ data: { id: "e" + (i++), source: e.parent, target: e.child, kind: e.kind, via: e.via || "" } });
  const nStacked = [...stacked].filter((n) => !drawn.has(n)).length;
  $("#gcount").textContent = ` · ${keep.size} problems (${shown.length} drawn` + (nStacked ? `, ${nStacked} in ${nStacks} stacks` : "") + `), ${i} edges${note}`;
  window.explore.graph = { problems: keep.size, drawn: shown.length, stacks: nStacks, stacked: nStacked,
    stackMembers: [...stacked].filter((n) => !drawn.has(n)) };
  if (cy) cy.destroy();
  cy = cytoscape({
    container: $("#cy"), elements: els, minZoom: 0.05,
    style: [
      { selector: "node", style: { label: "data(label)", "text-wrap": "wrap", "text-overflow-wrap": "anywhere", "text-max-width": 140, "font-size": 10, "text-valign": "center", "text-halign": "center",
        width: 150, height: 34, shape: "round-rectangle", "background-color": "#fff", color: "#1d2329", "text-outline-width": 0,
        "border-width": 1, "border-color": "#7b848d" } },
      { selector: "node[att = 'bad']", style: { "background-color": "#fdecec", "border-color": "#d64545", "border-width": 2, color: "#9b1c1c" } },
      { selector: "node[att = 'unmet']", style: { "border-style": "dashed", "border-color": "#b7791f", "border-width": 2 } },
      { selector: "node[att = 'dep']", style: { color: "#66707a", "background-color": "#f4f6f8" } },
      { selector: "node[stack = 1]", style: { shape: "round-rectangle", width: 110, height: 30, "background-color": "#f4f6f8", "border-color": "#9aa0a6",
        "border-width": 1, "font-size": 11, "underlay-color": "#c9ced3", "underlay-opacity": 1, "underlay-padding": 3, "underlay-shape": "round-rectangle" } },
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
  const stackOf = new Map([...stacks.values()].map((st) => [st.id, st]));
  cy.on("tap", "node", (e) => {
    const st = stackOf.get(e.target.id());
    if (!st) return side(problemDetail(e.target.id()));
    side(table(st.members.map((m) => ({ problem: m })), ["problem"]).then((t) =>
      `<h2>${st.members.length} × ${esc(SZS_SHORT[st.code] || st.code)} under ${link("problem", st.parent, shortName(st.parent))}</h2>` +
      `<p class="muted">leaves (no children of their own) by ${esc(st.kind)} edges</p>` +
      `<p><button type="button" id="gexpand">Expand: draw them one by one</button></p>` + t)).then(() => {
      const b = $("#gexpand");
      if (b) b.addEventListener("click", () => { gExpanded.add(st.parent); window.explore.redrawGraph(); });
    });
  });
  cy.on("dbltap", "node", (e) => { if (!stackOf.has(e.target.id())) location.hash = href("graph", e.target.id()); });
  cy.on("tap", "edge", (e) => { const d = e.target.data();
    side(dl({ parent: d.source, child: d.target, kind: d.kind, via: d.via || null }).then((x) => "<h2>Edge</h2>" + x)); });
  // A wide level makes "fit" unreadable: then zoom in on the focus instead.
  if (cy.zoom() < 0.5 && cy.getElementById(focus).length) { cy.zoom(0.8); cy.center(cy.getElementById(focus)); }
  if (focus && cy.getElementById(focus).length) await side(problemDetail(focus));
}

registerView({ id: "graph", title: "Graph", nav: 20, render: graph });
