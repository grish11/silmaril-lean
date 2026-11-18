// ---------- verification progress: every family of the project, by status and by dimension ----------
// `#/progress`. The families are the children of the project's root group; a family's problems
// are the problems (not groups) reachable from it through `children` edges. Each is counted once
// per family, in exactly one status column:
//   holds        the summary verdict is holds (THM, or derived along proved edges)
//   fails        the summary verdict is fails
//   open         neither (OPN, UNK, SAT/CSA that do not settle the problem's expectation)
// and, apart from those columns (a problem in them is also in one of the three):
//   deprecated     marked wrong by a deprecation record
//   expected open  an expected_open marking (a metatheoretic reason)
//   findings       a finding record (error, spec_bug, model_gap, unclear)
//   axiomatic      some answer of the problem uses an axiom other than propext, Classical.choice
//                  and Quot.sound (sorryAx, a native-evaluation axiom, a project axiom)
//   not kernel     settled, but the deriving tier is not `kernel` (compiled, tool, external)
//   detached       a detached problem (a statement kept out of the problem graph, with a reason)
//
// Dimensions. A project says which kind of evidence a problem is with groups named
// `<prefix>.dimension.<d>`, for d in DIMENSIONS (inventory, decomposition, semantic): every
// problem reachable from such a group is in dimension d. The page cross-tabulates families and
// dimensions; a problem in no dimension group is `unclassified`, and one in several is counted in
// each (the page says how many). Nothing here reads problem names or titles to classify.
//
// Pure tallies (`progressTally`) are DOM-free so the Node tests can load this file.

const PROGRESS_DIMENSIONS = Object.freeze([
  { key: "inventory", title: "Inventory and import", text: "what the artifacts are: files pinned by hash, ELF parses, symbol tables, exports, imported objects" },
  { key: "decomposition", title: "Function decomposition", text: "where the functions are: an executable section partitioned into symbol-table function extents and explicit gaps, checked on the file's bytes" },
  { key: "semantic", title: "Semantic and function correctness", text: "what the code does: contracts, specifications, effects, refinements" },
]);
const PROGRESS_STANDARD_AXIOMS = new Set(["propext", "Classical.choice", "Quot.sound"]);

// Every problem reachable from `start` through `kids` (a Map name -> [child]), groups excluded.
function progressLeaves(start, kids, isGroup) {
  const seen = new Set([start]), out = new Set(), stack = [start];
  while (stack.length) {
    const n = stack.pop();
    for (const c of kids.get(n) || []) {
      if (seen.has(c)) continue;
      seen.add(c);
      if (isGroup(c)) stack.push(c); else out.add(c);
    }
  }
  return out;
}

// One row of counts for a set of problem names. `info(name)` gives
// { verdict, deprecated, expectedOpen, finding, axiomatic, tier, detached } (missing = unknown).
function progressTally(names, info) {
  const t = { problems: 0, holds: 0, fails: 0, open: 0, deprecated: 0, expectedOpen: 0, findings: 0, axiomatic: 0, notKernel: 0, detached: 0 };
  for (const n of names) {
    const i = info(n) || {};
    t.problems++;
    if (i.verdict === "holds") t.holds++; else if (i.verdict === "fails") t.fails++; else t.open++;
    if (i.deprecated) t.deprecated++;
    if (i.expectedOpen) t.expectedOpen++;
    if (i.finding) t.findings++;
    if (i.axiomatic) t.axiomatic++;
    if ((i.verdict === "holds" || i.verdict === "fails") && i.tier && i.tier !== "kernel") t.notKernel++;
    if (i.detached) t.detached++;
  }
  return t;
}

// The dimension of each problem: name -> Set(dimension key), from the `<prefix>.dimension.<d>` groups.
function progressDimensions(groups, kids, isGroup) {
  const dims = new Map();
  for (const g of groups) {
    const m = /\.dimension\.([a-z]+)$/.exec(g);
    if (!m || !PROGRESS_DIMENSIONS.some((d) => d.key === m[1])) continue;
    for (const n of progressLeaves(g, kids, isGroup)) {
      if (!dims.has(n)) dims.set(n, new Set());
      dims.get(n).add(m[1]);
    }
  }
  return dims;
}

if (typeof module !== "undefined") module.exports = { progressLeaves, progressTally, progressDimensions, PROGRESS_DIMENSIONS };

if (typeof registerView === "function") {
  const bar = (t) => {
    if (!t.problems) return "";
    const w = (n) => (100 * n / t.problems).toFixed(2);
    return `<span class="pbar" title="${t.holds} holds, ${t.fails} fails, ${t.open} open of ${t.problems}" style="display:inline-flex;width:140px;height:10px;border:1px solid #8884;vertical-align:middle">` +
      `<span style="width:${w(t.holds)}%;background:#2a8a3e"></span><span style="width:${w(t.fails)}%;background:#c0392b"></span><span style="width:${w(t.open)}%;background:#9996"></span></span>`;
  };
  const num = (n, cls) => n ? `<td class="num${cls ? " " + cls : ""}">${n}</td>` : '<td class="num muted">0</td>';
  const row = (label, t) => `<tr><td>${label}</td><td class="num">${t.problems}</td>${num(t.holds)}${num(t.fails)}${num(t.open)}<td>${bar(t)}</td>` +
    `${num(t.deprecated)}${num(t.expectedOpen)}${num(t.findings)}${num(t.axiomatic, t.axiomatic ? "err" : "")}${num(t.notKernel)}${num(t.detached)}</tr>`;
  const HEAD = '<thead><tr><th></th><th class="num">problems</th><th class="num">holds</th><th class="num">fails</th><th class="num">open</th><th></th>' +
    '<th class="num" title="marked wrong; kept for the record">deprecated</th><th class="num" title="expected_open marking">expected open</th>' +
    '<th class="num" title="finding records">findings</th><th class="num" title="an answer uses an axiom beyond propext, Classical.choice, Quot.sound">axiomatic</th>' +
    '<th class="num" title="settled at a tier other than kernel">not kernel</th><th class="num" title="detached statements">detached</th></tr></thead>';

  async function progress(arg, ctx) {
    const { esc, link } = Explorer.ui;
    const has = (t) => tables.has(t);
    if (!has("problems") || !has("edges")) return '<p class="muted">This database has no problems or edges.</p>';
    const proj = (await ctx.tq("projects", "SELECT name, root FROM projects WHERE origin = 'local' LIMIT 1"))[0];
    if (!proj || !proj.root) return '<p class="muted">The project has no root group.</p>';
    const idx = await problemIndex();
    const kindOf = new Map((await ctx.q("SELECT name, kind, detached FROM problems")).map((r) => [r.name, r]));
    const isGroup = (n) => (kindOf.get(n) || {}).kind === "group";
    const kids = new Map();
    for (const e of await ctx.q("SELECT parent, child FROM edges WHERE kind = 'sub' AND record_kind = 'children'")) {
      if (!kids.has(e.parent)) kids.set(e.parent, []);
      kids.get(e.parent).push(e.child);
    }
    const tier = new Map(has("summary") ? (await ctx.q("SELECT problem, tier FROM summary")).map((r) => [r.problem, r.tier]) : []);
    const axiomatic = new Set();
    if (has("answer_axioms") && has("answers"))
      for (const r of await ctx.q("SELECT DISTINCT a.problem, x.axiom FROM answers a JOIN answer_axioms x ON x.decl = a.decl"))
        if (!PROGRESS_STANDARD_AXIOMS.has(r.axiom)) axiomatic.add(r.problem);
    const info = (n) => {
      const e = idx.byName && idx.byName.get(n);
      const r = e ? e.row : {};
      return { verdict: r.verdict, deprecated: r.deprecated, expectedOpen: r.expectedOpen, finding: r.finding,
        axiomatic: axiomatic.has(n), tier: tier.get(n), detached: !!(kindOf.get(n) || {}).detached };
    };
    const families = (kids.get(proj.root) || []).filter(isGroup);
    const famLeaves = families.map((f) => [f, progressLeaves(f, kids, isGroup)]);
    const titles = await problemTitles(families);
    const famLabel = (f) => link("problem", f) + (titles.get(f) ? `<div class="muted" style="max-width:420px">${esc(titles.get(f))}</div>` : "");
    const all = progressLeaves(proj.root, kids, isGroup);
    const groups = [...kindOf.keys()].filter(isGroup);
    const dims = progressDimensions(groups, kids, isGroup);
    let h = `<h2>Verification progress</h2><p class="muted">Every family of ${esc(proj.name)} (the children of ${link("problem", proj.root)}), ` +
      "with each problem counted once per family. holds + fails + open = problems; the columns after the bar are counted apart. " +
      '<a href="#/statuses">What the status codes mean</a>.</p>';
    h += `<div class="tablebox"><table class="progress">${HEAD}<tbody>` +
      famLeaves.map(([f, ls]) => row(famLabel(f), progressTally(ls, info))).join("") +
      row("<b>all (distinct)</b>", progressTally(all, info)) + "</tbody></table></div>";
    if (dims.size) {
      h += "<h2>By dimension</h2><p class=\"muted\">Which kind of evidence each problem is, as the project's " +
        "<code>….dimension.&lt;d&gt;</code> groups say (nothing is inferred from names). " +
        PROGRESS_DIMENSIONS.map((d) => `<b>${esc(d.title)}</b>: ${esc(d.text)}.`).join(" ") + "</p>";
      const multi = [...all].filter((n) => (dims.get(n) || new Set()).size > 1).length;
      if (multi) h += `<p class="muted">${multi} problems are in more than one dimension and are counted in each.</p>`;
      for (const [f, ls] of [...famLeaves, [proj.root, all]]) {
        const by = Object.fromEntries([...PROGRESS_DIMENSIONS.map((d) => d.key), "unclassified"].map((k) => [k, []]));
        for (const n of ls) {
          const ds = dims.get(n);
          if (!ds || !ds.size) by.unclassified.push(n); else for (const d of ds) by[d].push(n);
        }
        h += `<h3>${f === proj.root ? "All families" : famLabel(f)}</h3><div class="tablebox"><table class="progress">${HEAD}<tbody>` +
          PROGRESS_DIMENSIONS.map((d) => row(esc(d.title), progressTally(by[d.key], info))).join("") +
          (by.unclassified.length ? row('<span class="muted">unclassified</span>', progressTally(by.unclassified, info)) : "") +
          "</tbody></table></div>";
      }
    } else {
      h += '<p class="muted">The project declares no dimension groups (<code>….dimension.inventory</code>, <code>.decomposition</code>, <code>.semantic</code>).</p>';
    }
    return h;
  }
  registerView({ id: "progress", title: "Progress", nav: 15, render: progress });
}
