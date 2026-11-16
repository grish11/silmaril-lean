// and stops reading once a page of matches is found.
const PAGE = 100;
async function listPage(spec) {
  const total = tables.has(spec.table) ? (await q(`SELECT count(*) AS n FROM ${spec.table}`))[0].n : 0;
  const html = `<h2>${esc(spec.title)} (${total})</h2><div class="controls">
    <input type="text" id="filter" placeholder="filter: ${esc(spec.filter.join(", "))} contains…" size="44">
    <button id="prev">◀ previous</button><button id="next">next ▶</button><span id="range" class="muted"></span></div><div id="list"></div>`;
  const init = async () => {
    let off = 0, tok = 0;
    const draw = async () => {
      const mine = ++tok, f = $("#filter").value.trim().toLowerCase();
      const where = f ? "WHERE " + spec.filter.map((c) => `instr(lower(${c}), ?) > 0`).join(" OR ") : "";
      const rows = await q(`SELECT ${spec.select} ${where} ORDER BY ${spec.order} LIMIT ${PAGE + 1} OFFSET ${off}`, f ? spec.filter.map(() => f) : []);
      const html = await table(rows.slice(0, PAGE), spec.cols, Object.assign({ hints: spec.hints }, spec.table_opts));
      if (mine !== tok || !$("#list")) return;
      $("#list").innerHTML = html;
      $("#range").textContent = rows.length ? `rows ${off + 1}–${off + Math.min(rows.length, PAGE)}${f ? " of the matches" : ` of ${total}`}` : "";
      $("#prev").disabled = off === 0; $("#next").disabled = rows.length <= PAGE;
      updateStats();
    };
    let timer = null;
    $("#filter").addEventListener("input", () => { clearTimeout(timer); timer = setTimeout(() => { off = 0; draw(); }, 250); });
    $("#prev").addEventListener("click", () => { off = Math.max(0, off - PAGE); draw(); });
    $("#next").addEventListener("click", () => { off += PAGE; draw(); });
    await draw();
  };
  return { html, init };
}
function problems() {
  return listPage({ title: "Problems", table: "problems", order: "p.name", filter: ["p.name", "p.title", "p.module"], hints: { name: "problem" },
    select: "p.name, p.kind" + STATUS_COLS() + ", p.detached, p.title, p.module FROM problems p" + STATUS_JOINS(),
    cols: ["status", "name", "kind", "detached", "title", "module"],
    table_opts: { render: { status: statusBadge }, badges: false, nowrap: ["kind", "detached"] } });
}
function artifacts() {
  return listPage({ title: "Artifacts", table: "artifacts", order: "a.name, a.cid", filter: ["a.name", "a.cid", "a.type"], hints: { cid: "artifact" },
    select: "a.cid, a.name, a.type, a.size, a.registry, (SELECT group_concat(package || ':' || path, ' ') FROM artifact_paths ap WHERE ap.artifact = a.sid) AS paths, " +
      "(SELECT count(*) FROM value_sources v WHERE v.cid = a.cid) AS uses FROM artifacts a",
    cols: ["cid", "name", "type", "size", "registry", "paths", "uses"] });
}
function values() {
  return listPage({ title: "Values", table: "value_defs", order: "v.name", filter: ["v.name", "v.format", "v.module"], hints: { name: "value" },
    select: "v.name, v.format, (SELECT group_concat(cid, ' ') FROM value_sources s WHERE s.value = v.name) AS cids, v.parses, " +
      "v.module FROM value_defs v",
    cols: ["name", "format", "cids", "parses", "module"] });
}
function formats() {
  return listPage({ title: "Formats", table: "formats", order: "f.name", filter: ["f.name", "f.value_type", "f.module"], hints: { name: "format" },
    select: "f.name, f.input, f.value_type, f.base, f.printer, (SELECT group_concat(law, ',') FROM format_laws l WHERE l.format = f.name) AS laws, " +
      "(SELECT count(*) FROM value_sources s WHERE s.format = f.name) AS sources, f.module FROM formats f",
    cols: ["name", "input", "value_type", "base", "printer", "laws", "sources", "module"] });
}

function machines() {
  return listPage({ title: "Machines", table: "machines", order: "m.name", filter: ["m.name", "m.doc", "m.module"], hints: { name: "machine" },
    select: "m.name, m.n_states AS states, m.n_labels AS labels, m.n_edges AS edges, m.deterministic, " +
      "(SELECT count(*) FROM machine_bindings b WHERE b.machine = m.name) AS bindings, m.doc, m.module FROM machines m",
    cols: ["name", "states", "labels", "edges", "deterministic", "bindings", "doc", "module"] });
}

// ---------- details ----------

registerView({ id: "problems", title: "Problems", nav: 30, render: problems });
registerView({ id: "artifacts", title: "Artifacts", nav: 40, render: artifacts });
registerView({ id: "values", title: "Values", nav: 50, render: values });
registerView({ id: "formats", title: "Formats", nav: 60, render: formats });
registerView({ id: "machines", title: "Machines", nav: 70, render: machines });
