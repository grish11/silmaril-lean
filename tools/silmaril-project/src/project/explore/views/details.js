// Lists on detail pages are cut at `DETAIL` rows.
const DETAIL = 300;
async function problemDetail(name) {
  const p = (await q("SELECT * FROM problems WHERE name = ?", [name]))[0];
  if (!p) {
    const now = RENAMED[name];
    if (now && (await q("SELECT 1 AS x FROM problems WHERE name = ? LIMIT 1", [now])).length) {
      return `<p class="note">${esc(name)} was renamed to ${link("problem", now)}.</p>`;
    }
    return `<p class="err">no problem ${esc(name)}</p>`;
  }
  const s = (await tq("summary", "SELECT * FROM summary WHERE problem = ?", [name]))[0];
  await resolve([{ problem: name }], ["problem"], HINTS, false);
  const parts = StatusSemantics.splitName(name);
  const crumbs = parts.slice(0, -1).map((part, i) => `<a href="#/browse/${encodeURIComponent(parts.slice(0, i + 1).join("."))}"><code>${esc(part)}</code></a>`);
  let h = `<nav class="crumbs" aria-label="namespace"><a href="#/browse/">all</a>${crumbs.map((c) => " . " + c).join("")}</nav>`;
  h += `<h2>${p.kind === "group" ? "Group" : "Problem"} <code>${esc(name)}</code> ${statusBadge(name)}</h2>`;
  if (p.title) h += `<p>${esc(p.title)}</p>`;
  h += statusSentence(statusOf.get(name), p);
  h += `<p class="muted">${link("graph", name, "show in graph")}</p>`;
  h += await markings(name);
  h += await evidence(p, s);
  h += "<h2>Judgement</h2>" + await dl(Object.fromEntries(Object.entries(p).filter(([k, v]) => v !== null && k !== "title")), { name: "", spec: "", model: "" });
  if (s) h += `<p class="muted">summary tier: ${esc(s.tier)}</p>`;
  const args = await tq("problem_args", "SELECT pos, name, type FROM problem_args WHERE problem = ? ORDER BY pos LIMIT 100", [name]);
  if (args.length) h += "<h2>Arguments</h2>" + await table(args, null, { hints: { name: "" } });
  const ins = await tq("problem_inputs", "SELECT pos, value, cid FROM problem_inputs WHERE problem = ? ORDER BY pos LIMIT 100", [name]);
  if (ins.length) h += "<h2>Inputs</h2>" + await table(ins);
  const iargs = await tq("instance_args", "SELECT pos, term, value, cid FROM instance_args WHERE problem = ? ORDER BY pos LIMIT 100", [name]);
  if (iargs.length) h += "<h2>Instance arguments</h2>" + await table(iargs);
  h += '<h2 id="answers">Solutions / answers</h2>' + await tableOf(await first(DETAIL, "SELECT a.decl, a.status, a.source, a.tier, a.witness, a.module, " +
    "(SELECT group_concat(axiom, ', ') FROM answer_axioms x WHERE x.decl = a.decl) AS axioms FROM answers a WHERE a.problem = ? ORDER BY a.decl", [name]),
    ["decl", "status", "source", "tier", "witness", "axioms", "lean"],
    { render: { lean: (r) => sourceLink(r.module, r.decl) || '<span class="muted">—</span>' }, nowrap: ["status", "tier", "lean"] });
  h += "<h2>Statuses</h2>" + await tableOf(await first(DETAIL, `SELECT st.status, ${COARSE} AS verdict, st.via_kind, st.via, st.tier FROM statuses st ` +
    "LEFT JOIN szs z ON z.code = st.status LEFT JOIN problems p ON p.name = st.problem WHERE st.problem = ? ORDER BY st.status", [name]));
  h += "<h2>Children (edges out)</h2>" + await tableOf(await first(DETAIL, "SELECT e.child, e.kind, e.via, e.record_kind, e.record_name, s.summary, s.verdict " +
    "FROM edges e LEFT JOIN summary s ON s.problem = e.child WHERE e.parent = ? ORDER BY e.record_kind, e.record_name, e.pos", [name]),
    ["child", "kind", "via", "record_kind", "record_name"]);
  h += "<h2>Parents (edges in)</h2>" + await tableOf(await first(DETAIL, "SELECT parent, kind, via, record_kind, record_name FROM edges WHERE child = ? ORDER BY parent", [name]));
  const obl = await tq("value_sources", "SELECT value, pos, cid, format FROM value_sources WHERE obligation = ? LIMIT 100", [name]);
  if (obl.length) h += "<h2>Obligation of value sources</h2>" + await table(obl);
  return h;
}
function problemPage(name) { return problemDetail(name); }
// Names that changed, for links and bookmarks to the old name: the old name's page points to the
// new one when the open database has only the new one.
const RENAMED = Object.freeze({ "silmaril.selftest.all": "silmaril.all" });
// The status in words: the displayed code and what it means, the expectation and how the status
// compares to it, the markings that leave the problem out of the attention lists.
function statusSentence(row, p) {
  const st = row && StatusSemantics.problemStatus(row);
  if (!st) return "";
  const S = StatusSemantics, d = S.DISPLAY_CODES[st.code];
  const arity = st.arity == null ? "" : st.arity === 0 ? "It has no parameters." : `It has ${st.arity} parameter${st.arity === 1 ? "" : "s"}.`;
  let t = `<b>${esc(st.code)}</b> (${esc(d ? d.name : st.code)}): ${esc(d ? d.text : "")}. ${arity}`;
  if (st.expect) {
    t += ` Expected: <b>${esc(st.expectCode)}</b>` + (st.expectCode !== st.expect ? ` <span class="muted">(stored ${esc(st.expect)})</span>` : "") + " — " +
      esc(st.pending ? "less information than expected: nothing is established yet" : S.OUTCOMES[st.outcome].label) + ".";
  } else if (p.kind !== "group") t += " No expected status is recorded.";
  if (st.vacuous) t += " The statuses hold vacuously: THM and UNS together mean the argument carrier is empty.";
  if (st.deprecated) t += " Deprecated" + (st.deprecated === "self" ? "" : ` through its ${esc(st.deprecated)}`) + ": left out of the attention lists.";
  if (st.expectedOpen) t += ` Expected to stay open for a metatheoretic reason (<b>${esc(st.expectedOpen.reason)}</b>)${st.expectedOpen.note ? ": " + esc(st.expectedOpen.note) : ""}; left out of the attention lists while open.`;
  return `<p class="status-sentence">${t} <a href="#/statuses">What the codes mean</a>.</p>`;
}
// What the summary status rests on: the statuses with that code and how each was obtained (an
// answer theorem, a solved instance, an edge, a group), with links to the answers' sources. A
// status without evidence is not shown as established.
async function evidence(p, s) {
  let h = "";
  if (p.decl || p.module) {
    const link = sourceLink(p.module, p.decl);
    h += `<p>Statement: <code>${esc(p.decl || "?")}</code> in <code>${esc(p.module || "?")}</code>${link ? " · " + link : ""}</p>`;
  }
  if (!s) return h;
  const st = await tq("statuses", "SELECT status, via_kind, via, tier FROM statuses WHERE problem = ? AND status = ? ORDER BY via_kind, via LIMIT 20", [p.name, s.summary]);
  if (!st.length) {
    return h + `<p>${statusBadge(p.name)} <span class="muted">${s.summary === "OPN"
      ? `open: no Lean theorem answers or solves this problem (<code>@[answers "${esc(p.name)}" …]</code>, <code>@[solves …]</code>) and no instance, edge or decomposition establishes a status. The statement above is all there is; the open status is not a display error.`
      : "no recorded status has this code"}</span></p>`;
  }
  const answers = new Map((await inChunks("SELECT decl, module, tier, (SELECT group_concat(axiom, ', ') FROM answer_axioms x WHERE x.decl = a.decl) AS axioms FROM answers a WHERE decl IN ($)",
    st.filter((r) => r.via_kind === "answers" || r.via_kind === "solves").map((r) => r.via))).map((r) => [r.decl, r]));
  const VIA = { answers: "answer", solves: "solved by", refutes: "refuted by", instance: "from the instance", decomposition: "decomposed by", arity0: "from the closed problem's" };
  await resolve(st, ["via"], { via: "problem" }, false);
  const items = st.map((r) => {
    const a = answers.get(r.via);
    const what = a ? `<code>${esc(r.via)}</code>${a.axioms ? ` <span class="muted">(axioms: ${esc(a.axioms)})</span>` : ""} ${sourceLink(a.module, a.decl)}`
      : r.via_kind === "arity0" ? `${esc(r.via)} status` : cell("via", r.via, { via: "problem" });
    return `<li>${esc(VIA[r.via_kind] || r.via_kind)} ${what} <span class="muted">· ${esc(r.tier)} tier</span></li>`;
  });
  return h + `<div><b>Evidence</b> for ${statusBadge(p.name)}:<ul class="evidence">${items.join("")}</ul></div>`;
}
// What the markings say about a problem: its deprecation (directly or through a spec or a general
// problem) and what replaces it, what it replaces, and how its failure is classified. Deprecated
// problems and their counterexamples stay in the database and on every page; this links them to
// their successors.
async function markings(name) {
  let h = "";
  const dep = (await tq("deprecated_problems", "SELECT via_kind, via FROM deprecated_problems WHERE problem = ?", [name]))[0];
  if (dep) {
    const d = (await tq("deprecations", "SELECT name, kind, reason FROM deprecations WHERE name = ?", [dep.via]))[0];
    const reps = await tq("deprecation_replacements", "SELECT replacement, kind FROM deprecation_replacements WHERE name = ? ORDER BY pos", [dep.via]);
    await resolve(reps, ["replacement"], { replacement: "problem" }, false);
    const viaHint = { via: dep.via_kind === "instance" ? "problem" : "" };
    await resolve([dep], ["via"], viaHint, false);
    h += `<div class="note" role="note"><b>Deprecated</b>${dep.via_kind === "self" ? "" : ` through its ${esc(dep.via_kind)} ` + cell("via", dep.via, viaHint)}` +
      (d && d.reason ? `: ${esc(d.reason)}` : "") +
      (reps.length ? `. Replaced by ${reps.map((r) => (r.kind === "problem" ? cell("replacement", r.replacement, { replacement: "problem" }, true) : `<code>${esc(r.replacement)}</code> <span class="muted">(${esc(r.kind)})</span>`)).join(", ")}.` : ". No replacement is recorded.") +
      "</div>";
  }
  const prev = await tq("deprecation_replacements", "SELECT name FROM deprecation_replacements WHERE replacement = ? ORDER BY name LIMIT 50", [name]);
  if (prev.length) {
    await resolve(prev, ["name"], { name: "problem" }, false);
    h += `<p>Replaces ${prev.map((r) => cell("name", r.name, { name: "problem" }, true)).join(", ")} (deprecated).</p>`;
  }
  const f = (await tq("findings", "SELECT classification, note, pointer, fixed_in FROM findings WHERE problem = ?", [name]))[0];
  if (f) h += `<p>Finding: <b>${esc(f.classification)}</b>${f.note ? " — " + esc(f.note) : ""}` +
    `${f.pointer ? ` <span class="muted">(${esc(f.pointer)})</span>` : ""}${f.fixed_in ? ` fixed in ${esc(f.fixed_in)}` : ""}</p>`;
  return h;
}
async function valuePage(name) {
  const v = (await q("SELECT * FROM value_defs WHERE name = ?", [name]))[0];
  if (!v) return `<p class="err">no value ${esc(name)}</p>`;
  let h = `<h2>Value <code>${esc(name)}</code></h2>` + await dl(v, { name: "" });
  h += "<h2>Sources</h2>" + await tableOf(await first(DETAIL, "SELECT s.pos, s.cid, s.format, s.decl, s.obligation, m.summary, m.verdict FROM value_sources s " +
    "LEFT JOIN summary m ON m.problem = s.obligation WHERE s.value = ? ORDER BY s.pos", [name]));
  h += "<h2>Problems over this value</h2>" + await tableOf(await first(DETAIL, "SELECT problem, pos, 'input' AS via FROM problem_inputs WHERE value = ? " +
    "UNION ALL SELECT problem, pos, 'instance_arg' FROM instance_args WHERE value = ? ORDER BY 1", [name, name]));
  return h;
}
async function formatPage(name) {
  const f = (await q("SELECT * FROM formats WHERE name = ?", [name]))[0];
  if (!f) return `<p class="err">no format ${esc(name)}</p>`;
  let h = `<h2>Format <code>${esc(name)}</code></h2>` + await dl(f, { name: "" });
  h += "<h2>Laws</h2>" + await tableOf(await first(DETAIL, "SELECT law, proof, rel, module FROM format_laws WHERE format = ?", [name]));
  h += "<h2>Default of family</h2>" + await tableOf(await first(DETAIL, "SELECT name AS family, module FROM format_defaults WHERE format = ?", [name]));
  h += "<h2>Formats based on it</h2>" + await tableOf(await first(DETAIL, "SELECT name, value_type FROM formats WHERE base = ?", [name]), null, { hints: { name: "format" } });
  h += "<h2>Values in this format</h2>" + await tableOf(await first(DETAIL, "SELECT name AS value, decl, parses FROM value_defs WHERE format = ? ORDER BY name", [name]));
  h += "<h2>Value sources read with it</h2>" + await tableOf(await first(DETAIL, "SELECT value, pos, cid, obligation FROM value_sources WHERE format = ? ORDER BY value, pos", [name]));
  return h;
}
// ---------- generic rooted-graph analysis (shared by machines and control-flow graphs) ----------
// A provenance badge for a displayed analysis: checked by the Lean kernel (with the theorem that
// checks it), computed by a generator without a proof, or computed here in the browser.

registerView({ id: "problem", title: "Problem", tab: "problems", render: problemPage });
registerView({ id: "value", title: "Value", tab: "values", render: valuePage });
registerView({ id: "format", title: "Format", tab: "formats", render: formatPage });
