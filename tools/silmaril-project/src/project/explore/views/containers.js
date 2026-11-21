// The Containers view (docs/projects/containers-examples.md, experimental API): the worked
// container examples, each a registered problem of the group `containers.examples`.
//   #/containers               every example: what runs, under which profile, the registry's verdict
//   #/container/<problem>      one example: image, shape, digests, runtime, machine, clone policy,
//                              profile, specification, the proved run, the run computed now, the
//                              theorems and their sources, the command to try it
// The registry is the source of truth: which examples exist (the group's children), their
// expectations, verdicts and answers (with source links) come from the database. The
// description of each example (image, runtime, run, command) comes from `containers-examples.json`
// next to the page, written by `examples/containers/Examples.lean --json` (`make pages`); without
// it, the page shows the registry columns only.
(() => {
  const ui = Explorer.ui;
  const GROUP = "containers.examples";
  const DATA = "containers-examples.json";
  const KIND = "silmaril.containers.examples/v1";
  const esc = ui.esc;
  const code = (s) => s == null || s === "" ? "" : `<code>${esc(s)}</code>`;

  let dataP = null;
  // The descriptions, by problem name, or { missing } when there is no file next to the page.
  async function loadData() {
    if (!dataP) dataP = (async () => {
      let r;
      try { r = await fetch(DATA, { cache: "no-cache" }); }
      catch (e) { return { missing: `${DATA} could not be fetched (${e.message || e})` }; }
      if (r.status === 404) return { missing: `there is no ${DATA} next to this page` };
      if (!r.ok) throw new Error(`${DATA}: HTTP ${r.status}`);
      const j = await r.json();
      if (!j || j.kind !== KIND || !Array.isArray(j.examples)) throw new Error(`${DATA}: kind ${JSON.stringify(j && j.kind)}, expected ${KIND}`);
      return { byId: new Map(j.examples.map((e) => [e.id, e])) };
    })();
    try { return await dataP; } catch (e) { dataP = null; throw e; }
  }

  const statusOfRow = (p) => ({ summary: p.summary || "OPN", verdict: p.verdict || "unknown", expect: p.expect || null,
    arity: p.arity, established: p.established ? p.established.split(",") : [], deprecated: null });
  const ESTABLISHED = "(SELECT group_concat(st.status, ',') FROM statuses st WHERE st.problem = p.name) AS established";
  const fixtureBadge = (f) => f ? `<code data-fixture="${esc(f)}" title="${f === "real"
    ? "real bytes: an ELF in an OCI image, run by the LPS model of Linux"
    : "a small model program, run by a model machine"}">${esc(f)}</code>` : "";
  // The registry's verdict in words, next to its code: Proved / Refuted / Open from the verdict,
  // and whether that is what the problem's registered expectation says (`statusInfo`). An expected
  // refutation (a negative example) is neutral, not an alarm; a verdict contrary to the expectation is.
  function plainVerdict(r) {
    const s = statusOfRow(r), i = ui.statusInfo(s);
    const word = r.verdict === "holds" ? "Proved" : r.verdict === "fails" ? "Refuted" : "Open";
    const met = i && i.outcome === "match", contrary = i && (i.outcome === "contrary" || i.outcome === "error");
    const note = contrary ? "contrary to expectation" : met && r.verdict === "fails" ? "as expected: a negative example"
      : met ? "as expected" : "not yet established";
    const cls = contrary ? "fails" : r.verdict === "holds" && met ? "holds" : word === "Open" ? "unknown" : "";
    // an expected refutation: a neutral grey, neither the success nor the failure colour
    const style = cls ? "" : ` style="background:#6b7280"`;
    const label = `<span class="${cls ? "badge " + cls : "badge"}"${style} data-verdict="${esc(word.toLowerCase())}" ` +
      `data-expectation="${contrary ? "contrary" : met ? "met" : "pending"}" title="${esc(i ? i.title : "")}">${esc(word)}</span>`;
    return `${label} <span class="muted" data-note="1">${esc(note)}</span> ${ui.statusBadge(s)}`;
  }
  const experimental = `<p class="muted" data-experimental="1"><strong>Experimental API.</strong> ` +
    `Definitions and statements in <code>Silmaril.Containers</code> may change.</p>`;

  // The group's children, in order, with their registry rows.
  async function examples(ctx) {
    return ctx.q(
      "SELECT e.child AS name, e.pos, p.title, p.expect, p.arity, s.summary, s.verdict, " + ESTABLISHED + ", " +
      "(SELECT i.parent FROM edges i WHERE i.child = e.child AND i.kind = 'instance' LIMIT 1) AS shape " +
      "FROM edges e JOIN problems p ON p.name = e.child LEFT JOIN summary s ON s.problem = e.child " +
      "WHERE e.parent = ? AND e.record_kind = 'children' ORDER BY e.pos LIMIT 200", [GROUP]);
  }

  async function listPage(arg, ctx) {
    const rows = await examples(ctx);
    if (!rows.length) return `<h2>Containers</h2>${experimental}<p class="muted">This database has no group <code>${GROUP}</code>.</p>`;
    let data;
    try { data = await loadData(); } catch (e) { data = { missing: e.message }; }
    const d = (n) => (data.byId && data.byId.get(n)) || {};
    let h = `<h2>Containers</h2>${experimental}` +
      `<p>Each row is a container image, the way it is run, and what is verified about it. The verdict is the registry's; ` +
      `<em>real</em> examples are actual bytes run by the LPS model of Linux, <em>model</em> examples are small programs of a model machine. ` +
      `<em>Refuted, as expected</em> marks a negative example: the verification is meant to fail, and does. ` +
      `Try them: <code>lake env lean --run examples/containers/Examples.lean</code>.</p>`;
    if (data.missing) h += `<p class="muted">Descriptions are not available: ${esc(data.missing)}.</p>`;
    h += `<table id="containers-table"><thead><tr><th>example</th><th>kind</th><th>profile</th><th>specification</th>` +
      `<th>run</th><th>verdict</th></tr></thead><tbody>`;
    for (const r of rows) {
      const x = d(r.name);
      h += `<tr data-problem="${esc(r.name)}"><td><a href="#/container/${encodeURIComponent(r.name)}">${esc(x.title || r.title || r.name)}</a>` +
        `<div class="muted">${esc(r.name)}</div></td><td>${fixtureBadge(x.fixture)}</td><td>${esc(x.profile || "")}</td>` +
        `<td>${esc(x.spec || r.title || "")}</td><td>${esc(x.run || "")}</td><td class="nw">${plainVerdict(r)}</td></tr>`;
    }
    h += `</tbody></table>` + details();
    return h;
  }

  // The one place that says what each kind of example rests on.
  function details() {
    return `<details id="containers-status"><summary>What the verdicts rest on</summary><table><tbody>` +
      `<tr><th>real</th><td>The bytes of the image (SHA-256 checked in the kernel), read by the restricted OCI reader, loaded by LPS's x86-64 loader, ` +
      `run by the LPS model of Linux for every resolution of x86's undefined flags and every launch LPS admits. A Docker run of the same image is a test.</td></tr>` +
      `<tr><th>model</th><td>A small program of a model machine (<code>Mini</code>, <code>Tiny</code>) standing for the container's program; ` +
      `runs are those of the model. The HTTP example's response is parsed by the verified HTTP/1.1 parser.</td></tr>` +
      `<tr><th>every example</th><td>"No undefined behaviour" is part of every verified specification; threads are undefined under the sequential clone policy.</td></tr>` +
      `</tbody></table></details>`;
  }

  async function detailPage(name, ctx) {
    const [r] = (await examples(ctx)).filter((x) => x.name === name);
    if (!r) return `<h2>${esc(name)}</h2><p class="muted">Not an example of <code>${GROUP}</code>.</p>`;
    let data;
    try { data = await loadData(); } catch (e) { data = { missing: e.message }; }
    const x = (data.byId && data.byId.get(name)) || {};
    const args = await ctx.q("SELECT a.pos, pa.name AS binder, a.term FROM instance_args a " +
      "LEFT JOIN problem_args pa ON pa.problem = ? AND pa.pos = a.pos WHERE a.problem = ? ORDER BY a.pos LIMIT 50",
      [r.shape || "", name]).catch(() => []);
    const answers = await ctx.q("SELECT status, decl, module FROM answers WHERE problem = ? ORDER BY status LIMIT 20", [name]);
    const src = (m, decl) => typeof sourceLink === "function" ? sourceLink(m, decl) : "";
    const theorem = async (n) => {
      const [loc] = await ctx.q("SELECT module FROM decl_locations WHERE decl = ? LIMIT 1", [n]).catch(() => []);
      const s = loc ? src(loc.module, n) : "";
      return `<li>${code(n)}${s ? " " + s : ""}</li>`;
    };
    const ths = await Promise.all((x.theorems || []).map(theorem));
    const field = (k, v) => v ? `<tr><th>${esc(k)}</th><td>${v}</td></tr>` : "";
    let h = `<h2>${esc(x.title || r.title || name)} ${fixtureBadge(x.fixture)}</h2>${experimental}` +
      `<p id="container-verdict">Verdict (registry): ${plainVerdict(r)} — ${ui.link("problem", name)}</p>` +
      `<table id="container-detail"><tbody>` +
      field("image", esc(x.image || "")) +
      field("digests", (x.digests || []).map((d) => `${esc(d.name)} ${code(d.value)}`).join("<br>")) +
      field("shape", esc(x.shape || "")) +
      field("runtime", esc(x.runtime || "")) +
      field("machine", esc(x.machine || "")) +
      field("clone policy", esc(x.policy || "")) +
      field("profile", esc(x.profile || "")) +
      field("specification", esc(x.spec || r.title || "")) +
      field("expected", esc(x.expected || r.expect || "")) +
      field("proved run", esc(x.run || "")) +
      field("run computed now", x.executed ? esc(x.executed) : "") +
      field("source", x.source ? code(x.source) : "") +
      field("try it", code(x.command || "")) +
      `</tbody></table>`;
    if (ths.length) h += `<h3>Theorems</h3><ul id="container-theorems">${ths.join("")}</ul>`;
    h += `<h3>In the registry</h3><table><tbody>` +
      field("shape", r.shape ? ui.link("problem", r.shape) : "") +
      args.map((a) => field(a.binder || `#${a.pos}`, code(a.term))).join("") +
      answers.map((a) => field(`answer ${a.status}`, `${code(a.decl)} ${src(a.module, a.decl)}`)).join("") +
      `</tbody></table>`;
    if (data.missing) h += `<p class="muted">Descriptions are not available: ${esc(data.missing)}.</p>`;
    return h + details();
  }

  Explorer.registerView({ id: "containers", title: "Containers", nav: 68, render: listPage });
  Explorer.registerView({ id: "container", title: "Container", tab: "containers", render: detailPage });
})();
