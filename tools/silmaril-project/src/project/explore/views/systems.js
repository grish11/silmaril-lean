// The Systems view (docs/projects/consequence-systems.md): the registered consequence systems
// (Γ ⊢ φ, relations from contexts to conclusions), how each is built, and one page per system
// with the standard consequence problems about it, their outcomes, what each outcome means and
// the Lean answers (with their witnesses) that establish it.
//   #/systems                 every system, and what the standard questions mean
//   #/system/<name>           one system
// It reads the database only. A problem with no answer is unknown, never false; universality,
// context-universality and deriving a chosen ff are three different properties and are always
// named as such. A database without the consequence tables gets a notice instead of an error.
(() => {
  const ui = Explorer.ui;
  const LIMIT = 300;
  const PREFIX = "silmaril.shapes.consequence.";
  const SHAPE = (s) => (s || "").startsWith(PREFIX) ? s.slice(PREFIX.length) : s || "";
  const has = () => Explorer.tables().has("consequence_systems");
  const missing = `<p class="muted">This database has no consequence-system tables (built by an older <code>sil project</code>).</p>`;
  const code = (s) => s == null || s === "" ? "" : `<code>${ui.esc(s)}</code>`;
  // A Lean term, compact: qualified names keep their last two components (the full term is the
  // title, and the SQL tab has it too); keyword escapes «…» are dropped from the display only.
  const compactText = (t) => String(t).replace(/«([^»]*)»/g, "$1")
    .replace(/(?:[A-Za-z_][\w']*\.)+([A-Za-z_][\w']*\.[A-Za-z_][\w'!?]*)/g, "$1");
  const term = (t) => t == null || t === "" ? "" : `<code title="${ui.esc(t)}">${ui.esc(compactText(t))}</code>`;
  // A system's name relative to `base` (the namespace of the page's system), for readings.
  const rel = (n, base) => base && n.startsWith(base) && n.length > base.length ? n.slice(base.length) : n;
  const sysLink = (n) => `<a href="#/system/${encodeURIComponent(n)}">${ui.esc(n)}</a>`;

  // What each status means, by shape and by the arguments left free (`Silmaril.Project.Shapes.
  // Consequence.Thms` proves these readings). `{S}`, `{T}`, `{ctx}`, `{phi}`, `{ff}`, `{f}`, `{g}`
  // are the instance's arguments. A closed refutation is stored as UNS and reads as false.
  const READING = {
    derives: {
      "ctx phi": { THM: "{S} is universal: every context derives every conclusion", SAT: "{S} derives something",
        UNS: "{S} is empty: it derives nothing", CSA: "{S} is not universal", contingent: "{S} derives something, and is not universal" },
      phi: { THM: "{ctx} is context-universal in {S}: it derives every conclusion", SAT: "{ctx} derives something in {S}",
        UNS: "{ctx} derives nothing in {S}", CSA: "{ctx} does not derive every conclusion in {S}", contingent: "{ctx} derives some conclusions in {S}, not all" },
      ctx: { THM: "every context derives {phi} in {S}", SAT: "some context derives {phi} in {S}",
        UNS: "no context derives {phi} in {S}", CSA: "some context does not derive {phi} in {S}", contingent: "some contexts derive {phi} in {S}, some do not" },
      "": { THM: "{ctx} ⊢ {phi} holds in {S}", CSA: "{ctx} ⊢ {phi} does not hold in {S}" },
    },
    context_universal: {
      ctx: { THM: "every context derives every conclusion in {S} (universal)", SAT: "some context is context-universal in {S}",
        UNS: "no context is context-universal in {S}", CSA: "some context is not context-universal in {S}",
        contingent: "some contexts are context-universal in {S}, some are not" },
      "": { THM: "{ctx} is context-universal in {S}: it derives every conclusion", CSA: "{ctx} does not derive every conclusion in {S}" },
    },
    derives_bottom: {
      ctx: { THM: "every context derives {ff} in {S}", SAT: "some context derives {ff} in {S}",
        UNS: "no context derives {ff} in {S}", CSA: "some context does not derive {ff} in {S}",
        contingent: "some contexts derive {ff} in {S}, some do not" },
      "": { THM: "{ctx} derives {ff} in {S}", CSA: "{ctx} does not derive {ff} in {S}" },
    },
    sound_at: {
      "ctx phi": { THM: "{S} is sound for {T}: every consequence of {S} is one of {T}", CSA: "{S} is not sound for {T}: a counterexample" },
      "": { THM: "if {ctx} ⊢ {phi} in {S}, then in {T}", CSA: "{ctx} ⊢ {phi} in {S} but not in {T}" },
    },
    complete_at: {
      "ctx phi": { THM: "{S} is complete for {T}: every consequence of {T} is one of {S}", CSA: "{S} is not complete for {T}: a counterexample" },
      "": { THM: "if {ctx} ⊢ {phi} in {T}, then in {S}", CSA: "{ctx} ⊢ {phi} in {T} but not in {S}" },
    },
    translates_at: {
      "ctx phi": { THM: "({f}, {g}) preserves consequence from {S} to {T}", CSA: "({f}, {g}) does not preserve consequence from {S} to {T}: a counterexample" },
    },
    reflects_at: {
      "ctx phi": { THM: "({f}, {g}) reflects consequence from {T} back to {S}", CSA: "({f}, {g}) does not reflect consequence from {T} to {S}: a counterexample" },
    },
  };
  // The argument roles of each shape that a reading can leave free.
  const FREE_ROLES = ["ctx", "phi"];

  // The outcome: the shared status badge (which compares the stored code with the expected
  // status; for a closed problem by truth value), or "unknown" when there is no answer.
  function outcome(p) {
    if (!p.summary || p.summary === "OPN" || p.summary === "UNK") {
      return ui.badge("unknown", p.expect && p.expect !== "OPN" ? `unknown (expected ${p.expect})` : "unknown");
    }
    return ui.statusBadge({ summary: p.summary, verdict: p.verdict, expect: p.expect || null, arity: p.arity,
      deprecated: p.deprecated ? "self" : null });
  }
  function fill(t, args) {
    return t.replace(/\{(S|T|ctx|phi|ff|f|g)\}/g, (_, k) => args[k] || ({ S: "S", T: "T", ctx: "Γ", phi: "φ", ff: "ff", f: "f", g: "g" })[k]);
  }
  function reading(p, args) {
    const sh = READING[SHAPE(p.shape)];
    if (!sh) return "";
    const free = FREE_ROLES.filter((r) => (p.roles || []).includes(r) && !(r in args)).join(" ");
    const r = sh[free];
    // a closed refutation is stored as UNS (refuted at arity 0): the statement is false
    const s = p.arity === 0 && p.summary === "UNS" ? "CSA" : p.summary;
    return r && r[s] ? fill(r[s], args) : "";
  }

  // The fixed arguments of the given instances, by problem: role -> display text (a system by
  // its registered name, anything else by its Lean term), and the roles of each shape.
  async function argsOf(ctx, problems) {
    const out = new Map();
    if (!problems.length) return out;
    const marks = problems.map(() => "?").join(",");
    const rows = await ctx.q(
      "SELECT i.problem, r.role, i.term, c.name AS system FROM instance_args i " +
      "JOIN edges e ON e.child = i.problem AND e.kind = 'instance' " +
      "JOIN consequence_shape_roles r ON r.shape = e.parent AND r.pos = i.pos " +
      "LEFT JOIN consequence_systems c ON c.term = i.term " +
      `WHERE i.problem IN (${marks}) AND r.role <> 'type' LIMIT 5000`, problems);
    for (const r of rows) {
      if (!out.has(r.problem)) out.set(r.problem, {});
      out.get(r.problem)[r.role] = { text: r.system || r.term, system: r.system };
    }
    return out;
  }

  // Expectations, apart from truth: how many problems with an expected status meet it (an
  // expected negative result counts as met), are still unknown, or contradict it (the shared
  // `statusInfo` outcome).
  function tally(list) {
    const n = { match: 0, pending: 0, mismatch: 0, error: 0, none: 0 };
    for (const p of list) {
      const i = p.summary ? ui.statusInfo({ summary: p.summary, verdict: p.verdict, expect: p.expect || null, arity: p.arity }) : null;
      n[i ? i.outcome : p.expect && p.expect !== "OPN" ? "pending" : "none"]++;
    }
    return n;
  }
  function expectations(list) {
    const n = tally(list), with_ = n.match + n.pending + n.mismatch + n.error;
    if (!with_) return `<p class="muted">No problem here states an expected status.</p>`;
    const all = n.match === with_;
    return `<p class="expectations">${all ? "All " : ""}${n.match} of ${with_} expected statuses met` +
      (n.pending ? `, ${n.pending} not established yet` : "") + (n.mismatch + n.error ? `, <b>${n.mismatch + n.error} unexpected</b>` : "") +
      `<span class="muted"> — whether the project's expectations hold, not whether the statements are true: an expected
refutation that is refuted counts as met.</span></p>`;
  }

  async function listPage(arg, ctx) {
    if (!has()) return `<h2>Consequence systems</h2>${missing}`;
    const rows = await ctx.q(
      "SELECT c.name, c.title, c.op, c.decl, c.witness, c.contexts, c.conclusions, c.source, " +
      "(SELECT count(*) FROM consequence_operands o WHERE o.system = c.name) AS n_operands " +
      "FROM consequence_systems c ORDER BY c.name LIMIT " + (LIMIT + 1));
    // the problems of each system, once each (a problem naming it as S and as T counts once)
    const probs = new Map();
    for (const r of await ctx.q("SELECT DISTINCT cp.system, cp.problem, cp.expect, cp.summary, cp.verdict, p.arity " +
        "FROM consequence_problems cp JOIN problems p ON p.name = cp.problem LIMIT 20000")) {
      if (!probs.has(r.system)) probs.set(r.system, []);
      probs.get(r.system).push(r);
    }
    let h = `<h2>Consequence systems</h2>
<p class="muted">A consequence system <code>S : Ax → C → Prop</code> relates contexts to conclusions; <code>S Γ φ</code> reads
<code>Γ ⊢ φ</code>. A context may be a finite list <code>C₁, …, Cₙ</code>, a set or anything else, and <b>no structural rule is
implicit</b>: a system is reflexive, monotone or closed under cut only if a proof below says so. Every property is a problem
with Lean answers; a problem with no answer is <b>unknown</b>, not false.</p>
<div class="tablebox"><table id="systems-table"><thead><tr><th>system</th><th>title</th><th>construction</th><th>contexts → conclusions</th>
<th title="closed judgments: true / false / unknown">judgments</th><th title="problems with free arguments">questions</th><th title="expected statuses met / stated">expectations</th></tr></thead><tbody>`;
    for (const r of rows.slice(0, LIMIT)) {
      const how = r.op === "erase" ? `erase of ${term(r.witness)}` : r.op === "decl" ? term(r.decl)
        : `${ui.esc(r.op)} of ${r.n_operands} systems`;
      const ps = probs.get(r.name) || [];
      const cl = ps.filter((p) => p.arity === 0);
      const tru = cl.filter((p) => p.summary === "THM" || p.summary === "SAT").length;
      const fal = cl.filter((p) => p.summary === "UNS" || p.summary === "CSA").length;
      const n = tally(ps), stated = n.match + n.pending + n.mismatch + n.error;
      h += `<tr><td>${sysLink(r.name)}</td><td>${ui.esc(r.title || "")}</td><td>${how}</td>` +
        `<td>${term(r.contexts)} → ${term(r.conclusions)}</td>` +
        `<td>${cl.length ? `${tru} / ${fal} / ${cl.length - tru - fal}` : ""}</td><td>${ps.length - cl.length || ""}</td>` +
        `<td>${stated ? `${n.match} / ${stated}${n.mismatch + n.error ? ` <b>(${n.mismatch + n.error} unexpected)</b>` : ""}` : ""}</td></tr>`;
    }
    h += `</tbody></table></div>`;
    if (rows.length > LIMIT) h += `<p class="muted">showing the first ${LIMIT}; use the SQL tab for the rest</p>`;
    if (!rows.length) h += `<p class="muted">No consequence system is registered (<code>silmaril consequence_system</code>).</p>`;
    h += `<h3>The standard questions</h3>
<p class="muted">Each is a shape <code>${ui.esc(PREFIX)}…</code> whose last arguments are the context Γ and the conclusion φ; an instance
fixes the systems and asks about the arguments left free. The statuses mean (for <code>S</code> fixed, Γ and φ free):</p>
<div class="tablebox"><table id="systems-questions"><thead><tr><th>shape</th><th>statement</th><th>THM</th><th>SAT</th><th>UNS</th><th>CSA</th></tr></thead><tbody>` +
      [["derives", "Γ ⊢ φ in S", "ctx phi"], ["context_universal", "Γ derives every φ in S", "ctx"], ["derives_bottom", "Γ ⊢ ff in S", "ctx"],
        ["sound_at", "S Γ φ → T Γ φ", "ctx phi"], ["complete_at", "T Γ φ → S Γ φ", "ctx phi"],
        ["translates_at", "S Γ φ → T (f Γ) (g φ)", "ctx phi"], ["reflects_at", "T (f Γ) (g φ) → S Γ φ", "ctx phi"]]
        .map(([s, st, free]) => { const r = READING[s][free]; return `<tr><td>${ui.esc(s)}</td><td>${code(st)}</td>` +
          ["THM", "SAT", "UNS", "CSA"].map((k) => `<td>${ui.esc(r[k] ? fill(r[k], {}) : "")}</td>`).join("") + "</tr>"; }).join("") +
      `</tbody></table></div>
<p class="muted"><b>Universal</b> (every context derives every conclusion), <b>context-universal</b> (one context derives every
conclusion) and <b>derives ff</b> (a context derives a chosen conclusion) are different properties; they coincide only under
structural rules a system may not have. Fixing Γ and φ gives the member judgment <code>Γ ⊢ φ</code>, a closed proposition:
true or false. The judgments column counts these as true / false / unknown; the expectations column counts expected statuses
met, which is not the same as true. Constructions name their operands on the system's page.</p>`;
    return h;
  }

  async function detailPage(name, ctx) {
    if (!has()) return missing;
    const [c] = await ctx.q("SELECT * FROM consequence_systems WHERE name = ? LIMIT 1", [name]);
    if (!c) return `<p class="err">no consequence system ${ui.esc(name)}</p>`;
    const operands = await ctx.q("SELECT operand FROM consequence_operands WHERE system = ? ORDER BY pos LIMIT 100", [name]);
    const usedBy = await ctx.q("SELECT DISTINCT system FROM consequence_operands WHERE operand = ? ORDER BY system LIMIT 100", [name]);
    let h = `<h2>consequence system <code>${ui.esc(name)}</code></h2>`;
    if (c.title) h += `<p><b>${ui.esc(c.title)}</b></p>`;
    if (c.doc) h += `<p>${ui.esc(c.doc)}</p>`;
    const OPS = { decl: "a Lean definition", union: "union (⊔): Γ ⊢ φ in some operand", inter: "intersection (⊓): Γ ⊢ φ in every operand",
      diff: "difference (\\): Γ ⊢ φ in the first operand and not in the second", erase: "erasure of a witness system: Γ ⊢ φ iff some derivation exists (Nonempty)" };
    const src = typeof sourceLink === "function" ? sourceLink(c.module, c.decl) : "";
    const rows = [
      ["relates", `contexts ${term(c.contexts)} to conclusions ${term(c.conclusions)}`],
      ["construction", ui.esc(OPS[c.op] || c.op)],
      ["Lean definition", code(c.decl) + ` <span class="muted">in ${ui.esc(c.module)}</span>${src ? " " + src : ""}`],
    ];
    if (c.witness) rows.push(["witness system", term(c.witness) + ` <span class="muted">(a type of derivations of each Γ ⊢ φ)</span>`]);
    if (operands.length) rows.push(["operands", operands.map((o) => sysLink(o.operand)).join(", ")]);
    if (usedBy.length) rows.push(["used by", usedBy.map((u) => sysLink(u.system)).join(", ")]);
    if (c.source) rows.push(["source", ui.esc(c.source)]);
    h += `<dl>${rows.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join("")}</dl>`;

    const ps = await ctx.q(
      "SELECT cp.problem, cp.shape, cp.role, cp.expect, cp.title, cp.summary, cp.verdict, p.arity, " +
      "(SELECT group_concat(r.role, ' ') FROM consequence_shape_roles r WHERE r.shape = cp.shape) AS roles, " +
      "(SELECT 1 FROM deprecated_problems d WHERE d.problem = cp.problem LIMIT 1) AS deprecated " +
      "FROM consequence_problems cp JOIN problems p ON p.name = cp.problem " +
      "WHERE cp.system = ? ORDER BY cp.shape, p.arity DESC, cp.problem LIMIT " + LIMIT, [name]);
    // a problem naming this system in two roles (S and T of a translation into itself) is one row
    { const seen = new Map();
      for (const p of ps.splice(0)) { if (seen.has(p.problem)) seen.get(p.problem).role += ", " + p.role; else { seen.set(p.problem, p); ps.push(p); } } }
    for (const p of ps) p.roles = (p.roles || "").split(" ");
    const base = name.includes(".") ? name.slice(0, name.lastIndexOf(".") + 1) : "";
    const args = await argsOf(ctx, [...new Set(ps.map((p) => p.problem))]);
    const answers = new Map();
    if (ps.length) {
      const marks = ps.map(() => "?").join(",");
      for (const a of await ctx.q(`SELECT problem, status, witness, decl, module FROM answers WHERE problem IN (${marks}) ORDER BY problem, status LIMIT 2000`, ps.map((p) => p.problem))) {
        if (!answers.has(a.problem)) answers.set(a.problem, []);
        answers.get(a.problem).push(a);
      }
    }
    h += `<h3>Problems</h3><p class="muted">Every standard consequence problem that names this system, as <b>S</b> (the system asked about)
or <b>T</b> (the system it is compared with or translated into). The reading says what the outcome means for the arguments left free;
a CSA answer written <code>⟨Γ, φ, h⟩</code> keeps its counterexample. No answer means unknown, not false.</p>`;
    if (!ps.length) {
      h += `<p class="muted">No standard consequence problem names this system.</p>`;
    } else {
      h += expectations(ps);
      const table = (id, list) => {
        let t = `<div class="tablebox"><table id="${id}"><thead><tr><th>problem</th><th>question</th><th>as</th><th>fixed</th><th>outcome</th><th>reading</th><th>answers (witness)</th></tr></thead><tbody>`;
        for (const p of list) {
          const a = args.get(p.problem) || {};
          const plain = Object.fromEntries(Object.entries(a).map(([k, v]) => [k, v.system ? rel(v.system, base) : compactText(v.text)]));
          const own = p.role.split(", ");
          const fixed = Object.entries(a).filter(([k]) => !own.includes(k))
            .map(([k, v]) => `${ui.esc(k)} = ${v.system ? sysLink(v.system) : term(v.text)}`).join("<br>");
          const ans = (answers.get(p.problem) || []).map((x) => {
            let w = "";
            try { const ws = x.witness ? JSON.parse(x.witness) : null; if (Array.isArray(ws) && ws.length) w = ": " + ws.map(term).join(", "); } catch { /* shown without */ }
            const sl = typeof sourceLink === "function" ? sourceLink(x.module, x.decl) : "";
            return `${ui.esc(x.status)}${w} by ${code(x.decl)}${sl ? " " + sl : ""}`;
          }).join("<br>");
          t += `<tr><td>${ui.link("problem", p.problem)}<div class="muted">${ui.esc(p.title || "")}</div></td>` +
            `<td>${ui.esc(SHAPE(p.shape))}</td><td>${ui.esc(p.role)}</td><td>${fixed}</td>` +
            `<td class="nw">${outcome(p)}</td><td>${ui.esc(reading(p, plain))}</td><td>${ans || '<span class="muted">none</span>'}</td></tr>`;
        }
        return t + `</tbody></table></div>`;
      };
      const closed = ps.filter((p) => p.arity === 0), open = ps.filter((p) => p.arity !== 0);
      if (closed.length) {
        h += `<h4>Judgments: closed, true or false</h4><p class="muted">Every argument is fixed, so each is one proposition: THM or SAT
means true, UNS or CSA false (a refutation is stored as UNS), no answer unknown.</p>` + table("system-judgments", closed);
      }
      if (open.length) {
        h += `<h4>Questions over the free arguments: SZS status</h4><p class="muted">Some arguments (Γ, φ) are free: THM holds for all of
them, SAT for some, UNS for none, CSA fails for some, NOC (stored <code>contingent</code>) is SAT and CSA together.</p>` + table("system-problems", open);
      }
    }
    return h;
  }

  Explorer.registerView({ id: "systems", title: "Systems", nav: 66, render: listPage });
  Explorer.registerView({ id: "system", title: "System", tab: "systems", render: detailPage });
})();
