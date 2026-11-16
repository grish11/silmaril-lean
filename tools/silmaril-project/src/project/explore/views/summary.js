// The holds/fails/unknown coarsening of a status (as `sil project check`): UNS fails only for a
// closed (arity 0) problem; `contingent` fails; otherwise the `szs` table's verdict.
const COARSE = "CASE WHEN st.status = 'UNS' AND p.arity = 0 THEN 'fails' WHEN st.status = 'contingent' THEN 'fails' " +
  "ELSE coalesce(z.verdict, 'unknown') END";
// Every query here is an aggregate or has a LIMIT, so that a lazily loaded database only reads
// the pages it needs.
async function summary() {
  const proj = await tq("projects", "SELECT * FROM projects ORDER BY origin DESC, name LIMIT 50");
  const local = proj.find((p) => p.origin === "local");
  let h = "<h2>Project</h2>" + (local ? await dl(local) : '<p class="muted">no local project row</p>');
  const counts = [
    ...await tq("objects", "SELECT kind, count(*) AS n FROM objects GROUP BY kind"),
    ...await tq("artifacts", "SELECT 'artifact' AS kind, count(*) AS n FROM artifacts"),
    ...await tq("edges", "SELECT 'edge:' || kind AS kind, count(*) AS n FROM edges GROUP BY kind"),
    ...await tq("answers", "SELECT 'answer' AS kind, count(*) AS n FROM answers")];
  h += '<div class="grid"><div><h2>Objects by kind</h2>' + await table(counts) + "</div>";
  const vs = await tq("summary", "SELECT verdict, summary, count(*) AS n FROM summary GROUP BY 1, 2 ORDER BY 1, 2");
  const by = { holds: 0, fails: 0, unknown: 0 };
  for (const r of vs) by[r.verdict] = (by[r.verdict] || 0) + r.n;
  const tot = vs.reduce((a, r) => a + r.n, 0) || 1;
  h += "<div><h2>Derived verdicts (problems)</h2><div class=\"bar\">" +
    ["holds", "fails", "unknown"].map((v) => by[v] ? `<div class="${v}" style="width:${100 * by[v] / tot}%" title="${v} ${by[v]}"></div>` : "").join("") +
    "</div>" + await table(vs, ["summary", "verdict", "n"]) + "</div>";
  if (tables.has("statuses")) {
    h += "<div><h2>Statuses by SZS code</h2>" + await table(await q(
      `SELECT st.status AS code, z.name, ${COARSE} AS verdict, count(*) AS statuses, count(DISTINCT st.problem) AS problems ` +
      "FROM statuses st LEFT JOIN szs z ON z.code = st.status LEFT JOIN problems p ON p.name = st.problem GROUP BY 1, 3 ORDER BY 3, 1 LIMIT 200")) +
      '<p class="muted">holds = THM; fails = CSA, contingent, UNS of a closed problem; unknown = the rest.</p></div>';
  }
  h += "</div>";
  if (local && local.root) {
    await resolve([local], ["root"], HINTS, false);
    h += `<h2>Root</h2><p>${link("problem", local.root)}${verdictBadge(local.root)} · ${link("graph", local.root, "show in graph")}</p>`;
  }
  if (tables.has("objects") && tables.has("edges")) {
    const ng = (await q("SELECT count(*) AS n FROM objects WHERE kind = 'group'"))[0].n;
    if (ng) {
      // Names only: counting or tallying every group's children would read most of `edges`.
      const gs = await q("SELECT name AS group_name FROM objects WHERE kind = 'group' ORDER BY name LIMIT 100");
      h += `<h2>Groups (${ng})</h2>` + await table(gs, null, { hints: { group_name: "problem" } }) +
        (ng > 100 ? '<p class="muted">the first 100 groups</p>' : "") +
        '<p class="muted">a group\'s verdict vector is on its page (children, in order) and in the graph</p>';
    }
  }
  if (tables.has("summary")) {
    // With the index on summary(verdict, summary), CROSS JOIN keeps `summary` as the outer
    // loop and the scan ends after 100 rows. Without it, sorting or the detached filter would read
    // all of `summary` and `problems`, so take the first 100 in key order.
    const tuned = indexes.has("summary_verdict") || indexes.has("httpvfs_summary_verdict");
    const open = tuned
      ? await first(100, "SELECT s.problem AS name, s.summary, s.verdict FROM summary s CROSS JOIN problems p " +
        "WHERE p.name = s.problem AND s.verdict IN ('fails', 'unknown') AND p.detached = 0 ORDER BY s.verdict, s.summary")
      : await first(100, "SELECT problem AS name, summary, verdict FROM summary WHERE verdict IN ('fails', 'unknown')");
    h += `<h2>Problems not holding (${(by.fails || 0) + (by.unknown || 0)}, detached included)</h2>` +
      `<p class="muted">${tuned ? "not detached, fails first" : "in name order, detached included (the database predates the canonical indexes)"}</p>` +
      await tableOf(open, ["status", "name"], { hints: { name: "problem" }, badges: false, render: { status: (r) => statusBadge(r.name) } });
  }
  h += "<h2>Meta</h2>" + await table(await tq("meta", "SELECT * FROM meta LIMIT 100"));
  if (proj.length > 1) h += "<h2>Projects</h2>" + await table(proj, ["name", "origin", "version", "root", "url", "rev"]);
  return h;
}

// ---------- lists ----------
// A page of `PAGE` rows at a time; the filter is a case-insensitive substring of `filter` columns

registerView({ id: "summary", title: "Summary", nav: 10, render: summary });
