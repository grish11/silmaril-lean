// A column hint says which kind a column names. Cells are looked up by index (`IN (…)`, never a
// scan of a whole table); the SQL page looks up every string cell it shows.
const HINTS = { problem:"problem", parent:"problem", child:"problem", obligation:"problem", parses:"problem",
  root:"problem", group_name:"problem", record_name:"problem", focus:"problem", value:"value", format:"format",
  base:"format", cid:"artifact", artifact:"artifact", subject:"artifact", machine:"machine" };
const BADGE_COLS = new Set(["problem", "child", "name", "parent", "obligation", "parses"]);
// The columns `statusBadge` reads, for a query over `problems p`, from the tables this database has
// (all keyed by problem, so a lookup by name reads a few pages).
const STATUS_COLS = () => (tables.has("summary") ? ", s.summary, s.verdict" : "") + ", p.expect" +
  (tables.has("deprecated_problems") ? ", (SELECT via_kind FROM deprecated_problems d WHERE d.problem = p.name) AS deprecated" : "") +
  (tables.has("findings") ? ", (SELECT classification FROM findings f WHERE f.problem = p.name) AS finding" : "");
const STATUS_JOINS = () => tables.has("summary") ? " LEFT JOIN summary s ON s.problem = p.name" : "";
function noteStatus(name, r) {
  if (!r.summary) return;
  verdictOf.set(name, r.verdict); summaryOf.set(name, r.summary);
  statusOf.set(name, { summary: r.summary, verdict: r.verdict, expect: r.expect || null, deprecated: r.deprecated || null, finding: r.finding || null });
}
const LOOKUP = {
  problem: ["problems", () => "SELECT p.name AS n" + STATUS_COLS() + " FROM problems p" + STATUS_JOINS() + " WHERE p.name IN ($)"],
  value: ["value_defs", () => "SELECT name AS n FROM value_defs WHERE name IN ($)"],
  format: ["formats", () => "SELECT name AS n FROM formats WHERE name IN ($)"],
  artifact: ["artifacts", () => "SELECT cid AS n FROM artifacts WHERE cid IN ($) UNION SELECT sid FROM artifacts WHERE sid IN ($)"],
  machine: ["machines", () => "SELECT name AS n FROM machines WHERE name IN ($)"],
};
async function resolve(rows, cols, hints, all) {
  const want = Object.fromEntries(KINDS.map((k) => [k, new Set()]));
  for (const r of rows) for (const c of cols) {
    const v = r[c];
    if (typeof v !== "string" || !v || v.length > 300) continue;
    for (const k of hints[c] ? [hints[c]] : all ? KINDS : []) if (!known[k].has(v)) want[k].add(v);
  }
  for (const k of KINDS) {
    const names = [...want[k]];
    if (!names.length) continue;
    const [t, sql] = LOOKUP[k];
    // only a completed lookup is cached: an interrupted one (a superseded route) leaves no trace
    const found = tables.has(t) ? await inChunks(sql(), names, k === "artifact") : [];
    for (const n of names) known[k].set(n, false);
    for (const r of found) { known[k].set(r.n, true); if (k === "problem") noteStatus(r.n, r); }
  }
}
function cell(col, v, hints, badges) {
  if (v === null || v === undefined) return '<span class="muted">NULL</span>';
  if (v instanceof Uint8Array) return `<span class="muted">blob ${v.length} B</span>`;
  const s = String(v);
  for (const k of hints[col] ? [hints[col], ...KINDS] : KINDS) if (known[k].get(s)) {
    return link(k, s) + (k === "problem" && badges !== false && BADGE_COLS.has(col) ? verdictBadge(s) : "");
  }
  if (col === "verdict" && /^(holds|fails|unknown)$/.test(s)) return `<span class="muted">${esc(s)}</span>`;
  return esc(s);
}
// opts: hints (merged over HINTS), limit (rows shown), all (look up every string cell), more
// (the query was cut off; see `first`), render ({column: row -> HTML}, for computed columns such
// as `status: statusBadge`), badges (false: no status badge after problem links, when a status
// column shows it), nowrap (columns kept on one line; `status` always is), label ({column: header}).
async function table(rows, cols, opts) {
  opts = opts || {};
  if (!rows.length) return '<p class="muted">(none)</p>';
  cols = cols || Object.keys(rows[0]);
  const limit = opts.limit || 1000, shown = rows.slice(0, limit);
  const hints = Object.assign({}, HINTS, opts.hints);
  await resolve(shown, cols, hints, opts.all);
  const render = opts.render || {}, label = opts.label || {};
  const nowrap = new Set(["status", ...(opts.nowrap || [])]);
  const cls = (c, v) => [typeof v === "number" ? "num" : "", nowrap.has(c) ? "nw" : ""].filter(Boolean).join(" ");
  let h = '<div class="tablebox"><table><thead><tr>' + cols.map((c) => `<th${nowrap.has(c) ? ' class="nw"' : ""}>${esc(label[c] || c)}</th>`).join("") + "</tr></thead><tbody>";
  for (const r of shown) {
    h += "<tr>" + cols.map((c) => { const k = cls(c, r[c]);
      return `<td${k ? ` class="${k}"` : ""}>${render[c] ? render[c](r) : cell(c, r[c], hints, opts.badges)}</td>`; }).join("") + "</tr>";
  }
  h += "</tbody></table></div>";
  if (rows.length > limit) h += `<p class="muted">showing ${limit} of ${rows.length} rows</p>`;
  if (opts.more) h += `<p class="muted">showing the first ${rows.length} rows; there are more (use the SQL tab)</p>`;
  return h;
}
async function tableOf(r, cols, opts) { return table(r.rows, cols, Object.assign({ more: r.more }, opts)); }
async function dl(row, hints) {
  hints = Object.assign({}, HINTS, hints);
  await resolve([row], Object.keys(row), hints, false);
  return "<dl>" + Object.entries(row).map(([k, v]) => `<dt>${esc(k)}</dt><dd>${cell(k, v, hints)}</dd>`).join("") + "</dl>";
}

