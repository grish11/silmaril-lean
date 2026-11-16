// The holds/fails/unknown coarsening of a status (as `sil project check`): UNS fails only for a
// closed (arity 0) problem; `contingent` fails; otherwise the `szs` table's verdict.
const COARSE = "CASE WHEN st.status = 'UNS' AND p.arity = 0 THEN 'fails' WHEN st.status = 'contingent' THEN 'fails' " +
  "ELSE coalesce(z.verdict, 'unknown') END";

// The attention lists of the landing page (StatusSemantics.attentionOf), in order.
const ATTENTION = [
  { key: "contrary", title: "Contrary to expectation", text: "the established statuses contradict the expected status, or a finding classifies the refutation as a genuine error" },
  { key: "open", title: "Open", text: "nothing is established yet (OPN, UNK)" },
  { key: "weaker", title: "Less information than expected", text: "something is established and consistent with the expectation, but not the expectation itself (e.g. CSA where UNS is expected)" },
  { key: "stronger", title: "More information than expected", text: "the established statuses entail the expected status and say more (e.g. TAU where SAT is expected, or anything where OPN is expected)" },
];
const EXCLUDED = {
  deprecated: { title: "Deprecated", text: "marked wrong by a deprecation record; kept for the record" },
  "expected-open": { title: "Expected to stay open", text: "an expected_open marking gives a metatheoretic reason (e.g. independence, a consistency statement)" },
};
// A link to the namespace browser filtered by `params` (see views/browse.js).
function browseHref(path, params) {
  const qs = new URLSearchParams(params || {}).toString();
  return "#/browse/" + encodeURIComponent(path || "") + (qs ? "?" + qs : "");
}

// The glossary of displayed codes and outcomes (also the `#/statuses` page).
function glossary(counts) {
  const S = StatusSemantics;
  const row = (c) => {
    const d = S.DISPLAY_CODES[c];
    const n = counts && counts.get(c);
    return `<dt><span class="st">${esc(c)}</span></dt><dd>${esc(d.name)}: ${esc(d.text)}` +
      `${n ? ` · <a href="${browseHref("", { status: c })}">${n} problem${n === 1 ? "" : "s"}</a>` : ""}</dd>`;
  };
  return '<div class="grid"><div><h3>Without parameters</h3><dl class="glossary">' + ["THM", "CTH"].map(row).join("") + "</dl>" +
    "<h3>With parameters</h3><dl class=\"glossary\">" + ["TAU", "UNS", "SAT", "CSA", "NOC"].map(row).join("") + "</dl>" +
    "<h3>Either</h3><dl class=\"glossary\">" + ["OPN", "UNK"].map(row).join("") + "</dl></div>" +
    "<div><h3>Compared with the expected status</h3><dl class=\"glossary\">" +
    `<dt>${statusBadge({ summary: "UNS", arity: 1, expect: "THM" })}</dt><dd>${esc(S.OUTCOMES.contrary.label)}: ${esc(S.OUTCOMES.contrary.text)}</dd>` +
    `<dt>${statusBadge({ summary: "CSA", arity: 1, expect: "UNS" })}</dt><dd>${esc(S.OUTCOMES.weaker.label)}: ${esc(S.OUTCOMES.weaker.text)}</dd>` +
    `<dt>${statusBadge({ summary: "THM", arity: 1, expect: "SAT" })}</dt><dd>${esc(S.OUTCOMES.stronger.label)}: ${esc(S.OUTCOMES.stronger.text)}</dd>` +
    `<dt>${statusBadge({ summary: "THM", arity: 1, expect: "THM" })}</dt><dd>${esc(S.OUTCOMES.match.label)} (or nothing expected): no mark</dd>` +
    "</dl><p class=\"muted\">The database stores SZS codes (THM, UNS, SAT, CSA, contingent, OPN; " +
    `<a href="${SZS_SOURCE}" target="_blank" rel="noopener noreferrer">SZS ontology</a>). The displayed code depends on whether the problem has ` +
    "parameters: stored THM is TAU for a problem with parameters; stored UNS or CSA of a problem without parameters is CTH. A badge's title lists the stored codes. " +
    "An expectation is compared by what the statuses entail, assuming an inhabited argument carrier unless THM and UNS together show it empty.</p></div></div>";
}

async function statusesPage() {
  const idx = await problemIndex();
  const counts = new Map();
  for (const e of idx.list) if (e.kind !== "group") counts.set(e.st.code, (counts.get(e.st.code) || 0) + 1);
  return "<h2>What the status codes mean</h2>" + glossary(counts);
}

// A compact table of problems: status, name, title.
async function problemRows(list, limit) {
  const shown = list.slice(0, limit);
  if (!shown.length) return '<p class="muted">(none)</p>';
  return '<div class="tablebox"><table><thead><tr><th class="nw">status</th><th>problem</th><th>title</th></tr></thead><tbody>' +
    shown.map((e) => `<tr><td class="nw">${statusBadge(e.row)}</td><td>${link("problem", e.name)}</td><td>${esc(e.title || "")}</td></tr>`).join("") +
    "</tbody></table></div>" + (list.length > limit ? `<p class="muted">the first ${limit} of ${list.length}</p>` : "");
}

// Every query here is an aggregate, has a LIMIT, or is the shared problem index.
async function summary() {
  const proj = await tq("projects", "SELECT * FROM projects ORDER BY origin DESC, name LIMIT 50");
  const local = proj.find((p) => p.origin === "local");
  let h = local ? `<h2>${esc(local.name)}</h2>${local.description ? `<p>${esc(local.description)}</p>` : ""}` : "<h2>Project</h2>";
  const idx = tables.has("problems") ? await problemIndex() : { list: [] };
  if (idx.tooLarge) h += `<p class="muted">${idx.tooLarge} problems: too many to classify here; use the problem list and SQL.</p>`;
  const problemsOnly = idx.list.filter((e) => e.kind !== "group");
  const by = Object.fromEntries(ATTENTION.map((a) => [a.key, []]));
  const excluded = { deprecated: [], "expected-open": [] };
  for (const e of problemsOnly) {
    if (e.st.attention.list) by[e.st.attention.list].push(e);
    else if (e.st.attention.excluded) excluded[e.st.attention.excluded].push(e);
  }
  // within a list: closed problems first (they are single questions), then by name
  for (const k of Object.keys(by)) by[k].sort((a, b) => (a.arity === 0 ? 0 : 1) - (b.arity === 0 ? 0 : 1) || a.name.localeCompare(b.name));
  if (problemsOnly.length) {
    h += `<h2 id="attention">Needs attention</h2><p class="muted">${problemsOnly.length} problems. ` +
      `Open problems and problems whose statuses differ from what was expected. <a href="#/statuses">What the codes mean</a>.</p><div class="att">` +
      ATTENTION.map((a) => `<a class="card k-${a.key}" href="${browseHref("", { attention: a.key })}" title="${esc(a.text)}"><b>${by[a.key].length}</b>${esc(a.title)}</a>`).join("") +
      Object.entries(EXCLUDED).map(([k, x]) => `<a class="card k-excluded" href="${browseHref("", { excluded: k })}" title="${esc(x.text)}"><b>${excluded[k].length}</b>${esc(x.title)} <span class="muted">(not counted above)</span></a>`).join("") +
      "</div>";
    for (const a of ATTENTION) {
      if (!by[a.key].length) continue;
      const closed = by[a.key].filter((e) => e.arity === 0).length;
      h += `<h3 id="att-${a.key}">${esc(a.title)} (${by[a.key].length}${a.key === "open" ? `: ${closed} without parameters, ${by[a.key].length - closed} with` : ""})</h3>` +
        `<p class="muted">${esc(a.text)}. <a href="${browseHref("", { attention: a.key })}">browse by namespace</a></p>` + await problemRows(by[a.key], a.key === "open" ? 40 : 100);
    }
    const ex = Object.entries(excluded).filter(([, l]) => l.length);
    if (ex.length) h += "<h3>Left out of the lists above</h3><ul>" + ex.map(([k, l]) =>
      `<li><a href="${browseHref("", { excluded: k })}">${l.length} ${esc(EXCLUDED[k].title.toLowerCase())}</a> <span class="muted">— ${esc(EXCLUDED[k].text)}</span></li>`).join("") + "</ul>";
  }
  if (local && local.root) {
    await resolve([local], ["root"], HINTS, false);
    h += `<h2>Root</h2><p>${link("problem", local.root)}${verdictBadge(local.root)} · <a href="${browseHref("")}">browse by namespace</a> · ${link("graph", local.root, "graph")}</p>`;
  }
  h += "<details><summary><b>Counts, verdicts, groups and metadata</b></summary>";
  h += local ? await dl(local) : '<p class="muted">no local project row</p>';
  const counts = [
    ...await tq("objects", "SELECT kind, count(*) AS n FROM objects GROUP BY kind"),
    ...await tq("artifacts", "SELECT 'artifact' AS kind, count(*) AS n FROM artifacts"),
    ...await tq("edges", "SELECT 'edge:' || kind AS kind, count(*) AS n FROM edges GROUP BY kind"),
    ...await tq("answers", "SELECT 'answer' AS kind, count(*) AS n FROM answers")];
  h += '<div class="grid"><div><h2>Objects by kind</h2>' + await table(counts) + "</div>";
  const codes = new Map();
  for (const e of problemsOnly) codes.set(e.st.code, (codes.get(e.st.code) || 0) + 1);
  h += "<div><h2>Problems by status</h2>" + await table(StatusSemantics.DISPLAY_ORDER.filter((c) => codes.get(c)).map((c) =>
    ({ status: c, meaning: StatusSemantics.DISPLAY_CODES[c].text, problems: codes.get(c) })), ["status", "meaning", "problems"],
    { render: { status: (r) => `<a href="${browseHref("", { status: r.status })}"><span class="st">${esc(r.status)}</span></a>` } }) + "</div>";
  if (tables.has("statuses")) {
    h += "<div><h2>Stored statuses by SZS code</h2>" + await table(await q(
      `SELECT st.status AS code, z.name, ${COARSE} AS verdict, count(*) AS statuses, count(DISTINCT st.problem) AS problems ` +
      "FROM statuses st LEFT JOIN szs z ON z.code = st.status LEFT JOIN problems p ON p.name = st.problem GROUP BY 1, 3 ORDER BY 3, 1 LIMIT 200")) +
      '<p class="muted">As stored, before the reading by arity. holds = THM; fails = CSA, contingent, UNS of a closed problem; unknown = the rest.</p></div>';
  }
  h += "</div>";
  if (tables.has("objects") && tables.has("edges")) {
    const ng = (await q("SELECT count(*) AS n FROM objects WHERE kind = 'group'"))[0].n;
    if (ng) {
      const gs = await q("SELECT name AS group_name FROM objects WHERE kind = 'group' ORDER BY name LIMIT 100");
      h += `<h2>Groups (${ng})</h2>` + await table(gs, null, { hints: { group_name: "problem" } }) +
        (ng > 100 ? '<p class="muted">the first 100 groups</p>' : "");
    }
  }
  h += "<h2>Meta</h2>" + await table(await tq("meta", "SELECT * FROM meta LIMIT 100"));
  if (proj.length > 1) h += "<h2>Projects</h2>" + await table(proj, ["name", "origin", "version", "root", "url", "rev"]);
  h += "</details>";
  return h;
}

registerView({ id: "summary", title: "Summary", nav: 10, render: summary });
registerView({ id: "statuses", title: "Statuses", tab: "summary", render: statusesPage });
