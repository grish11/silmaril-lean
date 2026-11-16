// ---------- browse: problems by namespace, with status filters ----------
// `#/browse/<namespace>?status=OPN,CSA&attention=open&excluded=deprecated&outcome=weaker&q=json`:
// the problems under a dotted namespace, as a directory listing (child namespaces with their
// counts by displayed status, then the problems at this level). With a filter, every matching
// problem under the namespace is listed as well. Statuses and attention lists come from
// StatusSemantics (status.js) over the shared problem index (table.js `problemIndex`).
const BROWSE_LIMIT = 500;
let browseTree = { idx: null, tree: null };
// The route's namespace and filter, read from the raw hash (the router decodes the whole rest of
// the route, which would merge an encoded `&` of a search into the query).
function browseParse() {
  const raw = location.hash.replace(/^#\/?browse\/?/, "");
  const i = raw.indexOf("?");
  let path = i < 0 ? raw : raw.slice(0, i);
  try { path = decodeURIComponent(path); } catch (e) { /* keep it as written */ }
  const p = new URLSearchParams(i < 0 ? "" : raw.slice(i + 1));
  const list = (k) => p.getAll(k).flatMap((v) => v.split(",")).map((v) => v.trim()).filter(Boolean);
  return { path: path.replace(/\.$/, ""), codes: new Set(list("status")), outcomes: new Set(list("outcome")),
    attention: p.get("attention") || "", excluded: p.get("excluded") || "", q: (p.get("q") || "").trim() };
}
function browseQuery(f) {
  const p = new URLSearchParams();
  if (f.codes.size) p.set("status", [...f.codes].join(","));
  if (f.outcomes.size) p.set("outcome", [...f.outcomes].join(","));
  if (f.attention) p.set("attention", f.attention);
  if (f.excluded) p.set("excluded", f.excluded);
  if (f.q) p.set("q", f.q);
  return p.toString();
}
function browseFiltered(f) { return f.codes.size || f.outcomes.size || f.attention || f.excluded || f.q; }
// Whether an index entry passes the filter. Groups pass only an empty filter.
function browseMatch(e, f) {
  if (!browseFiltered(f)) return true;
  if (e.kind === "group") return false;
  if (!StatusSemantics.matchesFilter(e.st, { codes: f.codes, outcomes: f.outcomes })) return false;
  if (f.attention && (f.attention === "any" ? !e.st.attention.list : e.st.attention.list !== f.attention)) return false;
  if (f.excluded && (f.excluded === "any" ? !e.st.attention.excluded : e.st.attention.excluded !== f.excluded)) return false;
  if (f.q) {
    const t = f.q.toLowerCase();
    if (!e.name.toLowerCase().includes(t) && !String(e.title || "").toLowerCase().includes(t)) return false;
  }
  return true;
}
// Counts by displayed code, as small badges linking to the filtered listing.
function browseCounts(entries, path, f) {
  const by = new Map();
  for (const e of entries) if (e.kind !== "group") by.set(e.st.code, (by.get(e.st.code) || 0) + 1);
  return StatusSemantics.DISPLAY_ORDER.filter((c) => by.get(c)).map((c) => {
    const g = Object.assign({}, f, { codes: new Set([c]) });
    return `<a href="#/browse/${encodeURIComponent(path)}?${esc(browseQuery(g))}" title="${esc(StatusSemantics.DISPLAY_CODES[c].text)}"><span class="st">${esc(c)} ${by.get(c)}</span></a>`;
  }).join(" ");
}
async function browse() {
  const f = browseParse();
  const idx = await problemIndex();
  if (idx.tooLarge) return `<p class="muted">${idx.tooLarge} problems: too many to browse here; use the <a href="#/problems">problem list</a>.</p>`;
  if (browseTree.idx !== idx) browseTree = { idx, tree: StatusSemantics.namespaceTree(idx.list.map((e) => e.name)) };
  const node = StatusSemantics.namespaceNode(browseTree.tree, f.path);
  const qs = browseQuery(f);
  const to = (path) => `#/browse/${encodeURIComponent(path)}${qs ? "?" + esc(qs) : ""}`;
  const parts = f.path ? StatusSemantics.splitName(f.path) : [];
  let h = `<h2>Problems by namespace</h2><nav class="crumbs" aria-label="namespace"><a href="${to("")}">all</a>` +
    parts.map((p, i) => ` . ${i === parts.length - 1 ? `<span aria-current="page"><code>${esc(p)}</code></span>` : `<a href="${to(parts.slice(0, i + 1).join("."))}"><code>${esc(p)}</code></a>`}`).join("") + "</nav>";
  const S = StatusSemantics;
  h += `<form id="bfilter" class="controls" onsubmit="return false">
    <fieldset class="filters"><legend>status (<a href="#/statuses">meanings</a>)</legend>${S.DISPLAY_ORDER.filter((c) => c !== "CON").map((c) =>
      `<label title="${esc(S.DISPLAY_CODES[c].text)}"><input type="checkbox" name="status" value="${c}"${f.codes.has(c) ? " checked" : ""}> ${c}</label>`).join("")}</fieldset>
    <fieldset class="filters"><legend>compared with the expectation</legend>${["contrary", "weaker", "pending", "stronger", "match", "none"].map((o) =>
      `<label><input type="checkbox" name="outcome" value="${o}"${f.outcomes.has(o) ? " checked" : ""}> ${esc(o === "pending" ? "nothing established yet" : S.OUTCOMES[o].label)}</label>`).join("")}</fieldset>
    <label>needs attention <select name="attention"><option value="">—</option>${[["any", "any list"], ["contrary", "contrary"], ["open", "open"], ["weaker", "less than expected"], ["stronger", "more than expected"]].map(([v, t]) =>
      `<option value="${v}"${f.attention === v ? " selected" : ""}>${t}</option>`).join("")}</select></label>
    <label>left out <select name="excluded"><option value="">—</option>${[["any", "any reason"], ["deprecated", "deprecated"], ["expected-open", "expected to stay open"]].map(([v, t]) =>
      `<option value="${v}"${f.excluded === v ? " selected" : ""}>${t}</option>`).join("")}</select></label>
    <label>name or title <input type="text" name="q" value="${esc(f.q)}" size="24"></label>
    <button type="button" id="bclear">clear</button></form>`;
  if (!node) return h + `<p class="err">no namespace ${esc(f.path)}</p>`;
  const under = S.namespaceItems(node).map((n) => idx.byName.get(n)).filter(Boolean);
  const matching = under.filter((e) => browseMatch(e, f));
  const nprob = (l) => l.filter((e) => e.kind !== "group").length;
  h += `<p class="muted" id="bsummary">${nprob(matching)} of ${nprob(under)} problems${under.length > nprob(under) ? ` (and ${under.length - nprob(under)} groups)` : ""} under ${f.path ? `<code>${esc(f.path)}</code>` : "all namespaces"}${browseFiltered(f) ? " match the filter" : ""}. ` +
    `${browseCounts(matching, f.path, f)}</p>`;
  const kids = [...node.children.values()].map((c) => {
    const all = S.namespaceItems(c).map((n) => idx.byName.get(n)).filter(Boolean);
    return { c, all, m: all.filter((e) => browseMatch(e, f)) };
  }).filter((k) => !browseFiltered(f) || k.m.length).sort((a, b) => a.c.name.localeCompare(b.c.name));
  if (kids.length) {
    h += '<h3>Namespaces</h3><div class="tablebox"><table class="ns-table" id="bnamespaces"><thead><tr><th>namespace</th><th class="nw">problems</th><th class="nw">needs attention</th><th>by status</th></tr></thead><tbody>' +
      kids.map((k) => {
        const att = k.m.filter((e) => e.kind !== "group" && e.st.attention.list).length;
        return `<tr><td class="ns-name"><a href="${to(k.c.path)}">${esc(k.c.name)}.</a></td><td class="num nw">${nprob(k.m)}${browseFiltered(f) ? ` / ${nprob(k.all)}` : ""}</td>` +
          `<td class="num nw">${att ? `<a href="#/browse/${encodeURIComponent(k.c.path)}?attention=any">${att}</a>` : '<span class="muted">0</span>'}</td><td class="counts">${browseCounts(k.m, k.c.path, f)}</td></tr>`;
      }).join("") + "</tbody></table></div>";
  }
  const here = node.items.map((n) => idx.byName.get(n)).filter((e) => e && browseMatch(e, f));
  if (here.length) h += `<h3>Problems in <code>${esc(f.path || "(top level)")}</code></h3>` + browseRows(here);
  if (browseFiltered(f)) {
    h += `<h3>Every matching problem under ${f.path ? `<code>${esc(f.path)}</code>` : "all namespaces"} (${matching.length})</h3>` + browseRows(matching.slice(0, BROWSE_LIMIT)) +
      (matching.length > BROWSE_LIMIT ? `<p class="muted">the first ${BROWSE_LIMIT}</p>` : "");
  }
  const init = () => {
    const form = $("#bfilter");
    if (!form) return;
    const apply = () => {
      const fd = new FormData(form);
      const g = { path: f.path, codes: new Set(fd.getAll("status")), outcomes: new Set(fd.getAll("outcome")),
        attention: fd.get("attention") || "", excluded: fd.get("excluded") || "", q: String(fd.get("q") || "").trim() };
      const q2 = browseQuery(g);
      location.hash = "#/browse/" + encodeURIComponent(f.path) + (q2 ? "?" + q2 : "");
    };
    let timer = null;
    form.addEventListener("change", (e) => { if (e.target.name !== "q") apply(); });
    form.querySelector("input[name=q]").addEventListener("input", () => { clearTimeout(timer); timer = setTimeout(apply, 400); });
    $("#bclear").addEventListener("click", () => { location.hash = "#/browse/" + encodeURIComponent(f.path); });
    // keep the focus in the name field across the re-render a search causes
    if (f.q && document.activeElement === document.body) { const i = form.querySelector("input[name=q]"); i.focus(); i.setSelectionRange(i.value.length, i.value.length); }
  };
  return { html: h, init };
}
function browseRows(list) {
  if (!list.length) return '<p class="muted">(none)</p>';
  return '<div class="tablebox"><table class="browse-problems"><thead><tr><th class="nw">status</th><th>problem</th><th class="nw">params</th><th>title</th></tr></thead><tbody>' +
    list.map((e) => `<tr><td class="nw">${statusBadge(e.row)}</td><td>${link("problem", e.name)}${e.kind === "group" ? ' <span class="muted">group</span>' : ""}</td>` +
      `<td class="num nw">${e.arity == null ? "" : e.arity}</td><td>${esc(e.title || "")}</td></tr>`).join("") + "</tbody></table></div>";
}

registerView({ id: "browse", title: "Browse", nav: 15, render: browse });
