// ---------- the source page: #/source/<decl> ----------
// A Lean declaration where it is written, on a page of its own (linkable, no dialog): the source
// view of provenance.js for `decl`. The module comes from `decl_locations` when the database has
// it, else from the problem or answer whose declaration it is; a problem's name also leads to its
// declaration.
async function sourcePage(decl, ctx) {
  if (!decl) return '<p class="muted">Give a declaration: <code>#/source/&lt;name&gt;</code>.</p>';
  let module = ((await ctx.tq("decl_locations", "SELECT module FROM decl_locations WHERE decl = ?", [decl]))[0] || {}).module || null;
  let problem = (await ctx.q("SELECT name, module FROM problems WHERE decl = ? ORDER BY name LIMIT 1", [decl]))[0] || null;
  const answer = (await ctx.q("SELECT problem, module FROM answers WHERE decl = ?", [decl]))[0] || null;
  if (!module && !problem && !answer) {
    // a problem's name: show its declaration
    const p = (await ctx.q("SELECT decl FROM problems WHERE name = ? AND decl IS NOT NULL", [decl]))[0];
    if (p && p.decl !== decl) return sourcePage(p.decl, ctx);
  }
  module = module || (problem && problem.module) || (answer && answer.module);
  let h = `<h2>Lean source of <code>${esc(decl)}</code></h2>`;
  const about = [];
  if (problem) about.push(`the statement of problem ${link("problem", problem.name)}`);
  if (answer) about.push(`an answer to problem ${link("problem", answer.problem)}`);
  if (about.length) h += `<p>This declaration is ${about.join(" and ")}${module ? `, in module <code>${esc(module)}</code>` : ""}.</p>`;
  if (!module) return h + '<p class="muted">The database names no module for this declaration.</p>';
  const block = sourceBlock(module, decl, { pageLink: false });
  return h + (block || '<p class="muted">This page was generated without sources (<code>--source-url</code>, <code>--source-rev</code>): it cannot show the file.</p>');
}
registerView({ id: "source", title: "Lean source", tab: "problems", render: sourcePage });
