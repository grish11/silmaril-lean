function provBadge(kind, detail) {
  const t = { lean: "Lean kernel-checked", gen: "generator-computed, unchecked", browser: "browser-computed, unchecked" }[kind];
  return `<span class="prov prov-${kind}" title="${esc(detail || "")}">${t}${detail ? ": " + esc(detail) : ""}</span>`;
}
// Immediate dominators of `nodes` (ids) under `edges` ([from, to]) from the entries `roots`:
// with several roots, a synthetic root (id null) precedes them, as in Silmaril.Automata.Graph's
// `withRoot`. Returns { idom: Map(node -> parent or null), reachable: Set }. Iterative dataflow
// over dominator sets: small graphs only; an unreachable node has no entry in `idom`.
function dominators(nodes, edges, roots) {
  const ROOT = "\u0000root";
  const preds = new Map(nodes.map((n) => [n, []]));
  for (const [a, b] of edges) if (preds.has(b) && preds.has(a)) preds.get(b).push(a);
  const entry = roots.length === 1 ? roots[0] : ROOT;
  if (roots.length !== 1) { preds.set(ROOT, []); for (const r of roots) preds.get(r).push(ROOT); }
  const all = [...preds.keys()];
  // reachability from the entry
  const succ = new Map(all.map((n) => [n, []]));
  for (const [b, ps] of preds) for (const a of ps) succ.get(a).push(b);
  const reach = new Set([entry]), todo = [entry];
  while (todo.length) for (const b of succ.get(todo.pop())) if (!reach.has(b)) { reach.add(b); todo.push(b); }
  const R = all.filter((n) => reach.has(n));
  const dom = new Map(R.map((n) => [n, n === entry ? new Set([n]) : new Set(R)]));
  for (let changed = true; changed;) {
    changed = false;
    for (const n of R) {
      if (n === entry) continue;
      let acc = null;
      for (const p of preds.get(n)) if (reach.has(p)) acc = acc ? new Set([...acc].filter((x) => dom.get(p).has(x))) : new Set(dom.get(p));
      const next = new Set(acc || []); next.add(n);
      if (next.size !== dom.get(n).size) { dom.set(n, next); changed = true; }
    }
  }
  const idom = new Map();
  for (const n of R) {
    if (n === entry) { idom.set(n, null); continue; }
    const strict = [...dom.get(n)].filter((x) => x !== n);
    // the strict dominator dominated by all others has the largest dominator set
    const p = strict.reduce((best, x) => (best === undefined || dom.get(x).size > dom.get(best).size ? x : best), undefined);
    idom.set(n, p === ROOT ? null : p);
  }
  idom.delete(ROOT);
  return { idom, reachable: new Set(R.filter((n) => n !== ROOT)), synthetic: entry === ROOT };
}
// Draw a dominator tree (node -> parent) into `container`; unreachable nodes are listed apart.
function drawDomTree(container, nodes, idom, label, style) {
  const els = nodes.filter((n) => idom.has(n)).map((n) => ({ data: { id: "d:" + n, label: label(n) } }));
  let i = 0;
  for (const [n, p] of idom) if (p !== null && p !== undefined) els.push({ data: { id: "t" + (i++), source: "d:" + p, target: "d:" + n } });
  return cytoscape({ container, elements: els, wheelSensitivity: 0.2,
    layout: { name: "dagre", rankDir: "TB", nodeSep: 30, rankSep: 50 },
    style: [{ selector: "node", style: Object.assign({ label: "data(label)", "background-color": "#fff", "border-color": "#2f5d9e",
      "border-width": 1.5, shape: "round-rectangle", width: "label", height: 24, padding: 8, "font-size": 11,
      "text-valign": "center", "text-halign": "center" }, style || {}) },
      { selector: "edge", style: { "curve-style": "bezier", "target-arrow-shape": "triangle", width: 1.2,
        "line-color": "#9aa0a6", "target-arrow-color": "#9aa0a6" } }] });
}

// A machine document drawn from its canonical JSON (states, labels, edges, layers): states are
// nodes (initial: thick border; accepting: double border; rejecting: orange; error: red).
// Parallel edges between two states are merged into one edge, and self-loops are folded into
// their state (a "↺ n" badge), so large machines stay readable. Labels written as pairs
// "(a,b)" are grouped by their second component ("send|recv priority"). Clicking a state or an
// edge lists its transitions in full below the graph.
function compactLabels(ls) {
  const groups = new Map(), rest = [];
  for (const l of ls) {
    const m = /^\(([^,()]*),(.*)\)$/.exec(l);
    if (m) { if (!groups.has(m[2])) groups.set(m[2], []); groups.get(m[2]).push(m[1]); } else rest.push(l);
  }
  return [...[...groups].map(([b, as]) => `${as.join("|")} ${b}`), ...rest];
}
