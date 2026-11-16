// The Languages view (docs/projects/languages.md): the registered languages, their domains,
// measures and interpretations, and one page per language with its construction, provenance,
// identity and the standard language problems about it (membership examples among them).
//   #/languages[/?text=…&domain=…&op=…&deprecated=hide|only]   the tables, filtered
//   #/language/<name>                                          one language
// It reads the database only: an artifact (a Wasm module) is a CID and an interpretation here,
// never code to run. A database without the language tables (an older `sil project`) gets a
// notice instead of an error.
(() => {
  const ui = Explorer.ui;
  const LIMIT = 300;
  const SHAPE = (s) => (s || "").replace(/^silmaril\.shapes\.language\./, "");
  // What each status of an instance with only `x` free means (Shapes.Language.Thms).
  const READING = {
    member: { THM: "universal", SAT: "nonempty", UNS: "empty", CSA: "not universal", contingent: "nonempty, not universal" },
    subset_at: { THM: "included", CSA: "not included (counterexample)" },
    eq_at: { THM: "equal", CSA: "not equal (counterexample)" },
    bound_at: { THM: "bounded", CSA: "a member exceeds the bound" },
    eq_within_at: { THM: "equal to the restriction", CSA: "not equal (counterexample)" },
    bytes_member: { THM: "member", CSA: "not a member" },
  };

  // The outcome of a problem against its expected status: a negative result that was expected
  // is not a failure, and no answer is unknown, never false.
  function outcome(p) {
    const s = p.summary, e = p.expect;
    if (!s || s === "OPN" || s === "UNK") {
      return e && e !== "OPN" ? ui.badge("unknown", "unknown (expected " + e + ")") : ui.badge("unknown", "unknown");
    }
    if (e && e !== "OPN") {
      return e === s ? ui.badge("expected", s + ", as expected") : ui.badge("unexpected", s + ", expected " + e);
    }
    return ui.badge(p.verdict, s);
  }
  function reading(p) {
    const r = READING[SHAPE(p.shape)];
    const closed = p.arity === 0;
    if (closed && SHAPE(p.shape) === "member") return { THM: "member", CSA: "not a member", UNS: "not a member" }[p.summary] || "";
    return (r && r[p.summary]) || "";
  }
  const code = (s) => s == null ? "" : `<code>${ui.esc(s)}</code>`;
  const langLink = (n) => `<a href="#/language/${encodeURIComponent(n)}">${ui.esc(n)}</a>`;
  const opText = (r) => r.op === "regex" ? `regex (${r.semantics})` : r.op === "within" ? `within ${r.measure} ≤ ${r.bound}` : r.op;

  function filtersFrom(arg) {
    const f = new URLSearchParams(arg.replace(/^\?/, ""));
    return { text: f.get("text") || "", domain: f.get("domain") || "", op: f.get("op") || "", dep: f.get("deprecated") || "" };
  }

  async function listPage(arg, ctx) {
    if (!Explorer.tables().has("languages")) {
      return `<h2>Languages</h2><p class="muted">This database has no language tables (built by an older <code>sil project</code>).</p>`;
    }
    const f = filtersFrom(arg || "");
    const where = [], params = [];
    if (f.text) { where.push("(l.name LIKE ? OR coalesce(l.title,'') LIKE ? OR l.decl LIKE ?)"); params.push(`%${f.text}%`, `%${f.text}%`, `%${f.text}%`); }
    if (f.domain) { where.push("l.domain = ?"); params.push(f.domain); }
    if (f.op) { where.push("l.op = ?"); params.push(f.op); }
    if (f.dep === "hide") where.push("d.name IS NULL");
    if (f.dep === "only") where.push("d.name IS NOT NULL");
    const rows = await ctx.q(
      "SELECT l.name, l.title, l.domain, l.op, l.semantics, l.measure, l.bound, l.carrier, l.identity_hash, l.source, " +
      "d.name AS deprecated, (SELECT count(*) FROM language_problems lp WHERE lp.language IN (SELECT m.name FROM languages m WHERE m.identity_hash = l.identity_hash)) AS problems, " +
      // closed membership examples of this construction: accepted (THM), rejected (CSA/UNS), unknown (no answer)
      "(SELECT count(*) FROM language_problems lp JOIN problems pp ON pp.name = lp.problem WHERE pp.arity = 0 AND lp.role = 'L' AND lp.shape IN ('silmaril.shapes.language.member','silmaril.shapes.language.bytes_member') AND lp.summary = 'THM' AND lp.language IN (SELECT m.name FROM languages m WHERE m.identity_hash = l.identity_hash)) AS accepted, " +
      "(SELECT count(*) FROM language_problems lp JOIN problems pp ON pp.name = lp.problem WHERE pp.arity = 0 AND lp.role = 'L' AND lp.shape IN ('silmaril.shapes.language.member','silmaril.shapes.language.bytes_member') AND lp.summary IN ('CSA','UNS') AND lp.language IN (SELECT m.name FROM languages m WHERE m.identity_hash = l.identity_hash)) AS rejected, " +
      "(SELECT count(*) FROM language_problems lp JOIN problems pp ON pp.name = lp.problem WHERE pp.arity = 0 AND lp.role = 'L' AND lp.shape IN ('silmaril.shapes.language.member','silmaril.shapes.language.bytes_member') AND coalesce(lp.summary, 'OPN') NOT IN ('THM','CSA','UNS') AND lp.language IN (SELECT m.name FROM languages m WHERE m.identity_hash = l.identity_hash)) AS unknown, " +
      "(SELECT group_concat(operand, ', ') FROM (SELECT operand FROM language_operands o WHERE o.language = l.name ORDER BY pos)) AS operands " +
      "FROM languages l LEFT JOIN deprecations d ON d.name = l.name AND d.kind = 'language' " +
      (where.length ? "WHERE " + where.join(" AND ") + " " : "") + "ORDER BY l.name LIMIT " + (LIMIT + 1), params);
    const domains = await ctx.q("SELECT name, carrier, monoid, letters, doc FROM language_domains ORDER BY name LIMIT 200");
    const ops = await ctx.q("SELECT DISTINCT op FROM languages ORDER BY op LIMIT 20");
    const opt = (v, cur, label) => `<option value="${ui.esc(v)}"${v === cur ? " selected" : ""}>${ui.esc(label || v)}</option>`;
    let h = `<h2>Languages</h2>
<p class="muted">A language is a set over a domain, built by a Lean definition the registry generates or checks.
Membership, emptiness, inclusion and equality are undecidable in general: a question with no Lean answer is
<b>unknown</b>, and only a proof changes that. Nothing here runs an artifact.</p>
<form id="lang-filter" class="filters">
  <input name="text" placeholder="filter by name, title or definition" value="${ui.esc(f.text)}" size="34">
  <select name="domain">${opt("", f.domain, "every domain")}${domains.map((d) => opt(d.name, f.domain)).join("")}</select>
  <select name="op">${opt("", f.op, "every construction")}${ops.map((o) => opt(o.op, f.op)).join("")}</select>
  <select name="deprecated">${opt("", f.dep, "deprecated too")}${opt("hide", f.dep, "hide deprecated")}${opt("only", f.dep, "only deprecated")}</select>
  <button>filter</button>
</form>
<div class="tablebox"><table id="languages-table"><thead><tr><th>language</th><th>title</th><th>domain</th><th>construction</th><th>operands</th><th>examples: in / out / unknown</th><th>problems</th><th>identity</th></tr></thead><tbody>`;
    for (const r of rows.slice(0, LIMIT)) {
      h += `<tr><td>${langLink(r.name)}${r.deprecated ? " " + ui.badge("deprecated", "deprecated") : ""}</td>` +
        `<td>${ui.esc(r.title || "")}</td><td>${ui.esc(r.domain)}</td><td>${ui.esc(opText(r))}</td>` +
        `<td>${(r.operands || "").split(", ").filter(Boolean).map(langLink).join(", ")}</td>` +
        `<td>${r.accepted || r.rejected || r.unknown ? `${r.accepted} / ${r.rejected} / ${r.unknown}` : ""}</td><td>${r.problems || ""}</td><td><code title="${ui.esc(r.identity_hash)}">${ui.esc(r.identity_hash.slice(0, 12))}</code></td></tr>`;
    }
    h += `</tbody></table></div>`;
    if (rows.length > LIMIT) h += `<p class="muted">showing the first ${LIMIT}; narrow the filter or use the SQL tab</p>`;
    if (!rows.length) h += `<p class="muted">no language matches</p>`;
    h += `<h3>Domains</h3><div class="tablebox"><table><thead><tr><th>domain</th><th>carrier</th><th>monoid</th><th>letters</th><th>doc</th></tr></thead><tbody>` +
      domains.map((d) => `<tr><td><a href="#/languages/?domain=${encodeURIComponent(d.name)}">${ui.esc(d.name)}</a></td><td>${code(d.carrier)}</td>` +
        `<td>${d.monoid ? "yes" : ""}</td><td>${code(d.letters)}</td><td>${ui.esc(d.doc || "")}</td></tr>`).join("") + `</tbody></table></div>`;
    const ms = await ctx.q("SELECT name, domain, decl, codomain, doc FROM measures ORDER BY name LIMIT 200");
    h += `<h3>Measures</h3><div class="tablebox"><table><thead><tr><th>measure</th><th>domain</th><th>definition</th><th>into</th><th>doc</th></tr></thead><tbody>` +
      ms.map((m) => `<tr><td>${ui.esc(m.name)}</td><td>${ui.esc(m.domain)}</td><td>${code(m.decl)}</td><td>${code(m.codomain)}</td><td>${ui.esc(m.doc || "")}</td></tr>`).join("") + `</tbody></table></div>`;
    const is = await ctx.q("SELECT name, domain, decl, input, abi, environment, doc FROM language_interpretations ORDER BY name LIMIT 200");
    h += `<h3>Interpretations</h3><p class="muted">How an artifact's decoded value denotes a language; the ABI and environment occur in the definition.</p>` +
      `<div class="tablebox"><table><thead><tr><th>interpretation</th><th>domain</th><th>definition</th><th>reads</th><th>ABI</th><th>environment</th></tr></thead><tbody>` +
      is.map((i) => `<tr><td title="${ui.esc(i.doc || "")}">${ui.esc(i.name)}</td><td>${ui.esc(i.domain)}</td><td>${code(i.decl)}</td><td>${code(i.input)}</td><td>${code(i.abi)}</td><td>${code(i.environment)}</td></tr>`).join("") + `</tbody></table></div>`;
    return {
      html: h,
      init: () => {
        const form = document.getElementById("lang-filter");
        form.addEventListener("submit", (ev) => {
          ev.preventDefault();
          const p = new URLSearchParams();
          for (const [k, v] of new FormData(form)) if (v) p.set(k, v);
          location.hash = "#/languages/?" + p.toString();
        });
      },
    };
  }

  async function detailPage(name, ctx) {
    if (!Explorer.tables().has("languages")) return `<p class="muted">This database has no language tables (built by an older <code>sil project</code>).</p>`;
    const [l] = await ctx.q("SELECT * FROM languages WHERE name = ? LIMIT 1", [name]);
    if (!l) return `<p class="err">no language ${ui.esc(name)}</p>`;
    const [dom] = await ctx.q("SELECT carrier, monoid, letters FROM language_domains WHERE name = ? LIMIT 1", [l.domain]);
    const [dep] = await ctx.q("SELECT reason FROM deprecations WHERE name = ? AND kind = 'language' LIMIT 1", [name]);
    const succ = dep ? await ctx.q("SELECT replacement FROM deprecation_replacements WHERE name = ? ORDER BY pos LIMIT 50", [name]) : [];
    const operands = await ctx.q("SELECT operand FROM language_operands WHERE language = ? ORDER BY pos LIMIT 100", [name]);
    const usedBy = await ctx.q("SELECT DISTINCT language FROM language_operands WHERE operand = ? ORDER BY language LIMIT 100", [name]);
    const same = await ctx.q("SELECT name FROM languages WHERE identity_hash = ? AND name <> ? ORDER BY name LIMIT 50", [l.identity_hash, name]);
    let h = `<h2>language <code>${ui.esc(name)}</code>${dep ? " " + ui.badge("deprecated", "deprecated") : ""}</h2>`;
    if (l.title) h += `<p><b>${ui.esc(l.title)}</b></p>`;
    if (l.doc) h += `<p>${ui.esc(l.doc)}</p>`;
    if (dep) {
      h += `<p class="deprecation">Deprecated: ${ui.esc(dep.reason)}.` +
        (succ.length ? ` Superseded by ${succ.map((s) => langLink(s.replacement)).join(", ")}.` : " No successor.") +
        ` It is kept with its problems.</p>`;
    }
    const rows = [
      ["domain", `${ui.esc(l.domain)} — carrier ${code(dom ? dom.carrier : l.carrier)}${dom && dom.monoid ? ", a monoid" : ""}`],
      ["construction", ui.esc(opText(l))],
      ["Lean definition", code(l.decl) + ` <span class="muted">in ${ui.esc(l.module)}</span>`],
    ];
    if (l.format) rows.push(["format", ui.link("format", l.format)]);
    if (l.value) {
      const src = await ctx.q("SELECT pos, cid, format FROM value_sources WHERE value = ? ORDER BY pos LIMIT 10", [l.value]);
      rows.push(["artifact", ui.link("value", l.value) + src.map((s) => ` — bytes ${ui.link("artifact", s.cid, s.cid.slice(0, 20) + "…")} read as ${ui.esc(s.format)}`).join("")]);
    }
    if (l.interpretation) {
      const [i] = await ctx.q("SELECT decl, abi, environment, doc FROM language_interpretations WHERE name = ? LIMIT 1", [l.interpretation]);
      rows.push(["interpretation", ui.esc(l.interpretation) + (i ? `: ${code(i.decl)}, ABI ${code(i.abi) || "none declared"}, environment ${code(i.environment) || "none declared"}` : "")]);
    }
    if (l.regex) rows.push(["expression", `${code(l.regex)} with ${l.semantics === "list" ? "list (Accept.Regex)" : "monoid (Accept.MonoidRegex)"} semantics`]);
    if (l.measure) rows.push(["restriction", `${ui.esc(l.measure)} ≤ ${l.bound}`]);
    if (operands.length) rows.push([l.op === "regex" ? "leaves" : "operands", operands.map((o) => langLink(o.operand)).join(", ")]);
    if (usedBy.length) rows.push(["used by", usedBy.map((u) => langLink(u.language)).join(", ")]);
    if (l.source) rows.push(["source", ui.esc(l.source)]);
    h += `<dl>${rows.map(([k, v]) => `<dt>${k}</dt><dd>${v}</dd>`).join("")}</dl>`;
    h += `<h3>Identity</h3><p class="muted">The construction without any display name: renaming does not change it.
Equal sets built differently have different identities; their equality is a problem below, not a tag.</p>
<p>BLAKE3 <code>${ui.esc(l.identity_hash)}</code>${same.length ? ` — the same construction as ${same.map((s) => langLink(s.name)).join(", ")}` : ""}</p>
<pre class="identity">${ui.esc(JSON.stringify(JSON.parse(l.identity), null, 2))}</pre>`;
    const ps = await ctx.q(
      "SELECT lp.problem, lp.shape, lp.role, lp.expect, lp.title, lp.summary, lp.verdict, p.arity, " +
      "(SELECT group_concat(a.status || coalesce(': ' || a.witness, '') || ' by ' || a.decl, '; ') FROM answers a WHERE a.problem = lp.problem) AS answers " +
      "FROM language_problems lp JOIN problems p ON p.name = lp.problem " +
      "WHERE lp.language IN (SELECT m.name FROM languages m WHERE m.identity_hash = ?) ORDER BY p.arity, lp.shape, lp.problem LIMIT " + LIMIT, [l.identity_hash]);
    h += `<h3>Problems and examples</h3><p class="muted">Every standard language problem about this construction (under this name or another with the same identity).
Closed membership problems are the examples: THM means the sentence is in the language, CSA that it is not, each by the Lean answer shown;
no answer means unknown, not false.</p>`;
    if (!ps.length) {
      h += `<p class="muted">No standard language problem names this language.</p>`;
    } else {
      h += `<div class="tablebox"><table id="language-problems"><thead><tr><th>problem</th><th>question</th><th>as</th><th>outcome</th><th>reading</th><th>answers (witness)</th></tr></thead><tbody>` +
        ps.map((p) => `<tr><td>${ui.link("problem", p.problem)}<div class="muted">${ui.esc(p.title || "")}</div></td>` +
          `<td>${ui.esc(SHAPE(p.shape))}${p.arity === 0 ? " (closed)" : ""}</td><td>${ui.esc(p.role)}</td><td>${outcome(p)}</td>` +
          `<td>${ui.esc(reading(p))}</td><td>${ui.esc(p.answers || "none")}</td></tr>`).join("") + `</tbody></table></div>`;
    }
    return h;
  }

  const style = document.createElement("style");
  style.textContent = ".badge.expected { background:#3b7d5a; } .badge.unexpected { background:#b8860b; } .badge.deprecated { background:#6c757d; } " +
    "form.filters { display:flex; gap:8px; flex-wrap:wrap; margin:8px 0; } pre.identity { background:var(--panel); border:1px solid var(--line); " +
    "padding:8px 10px; max-height:40vh; overflow:auto; font:12px ui-monospace, monospace; } p.deprecation { border-left:3px solid #6c757d; padding-left:8px; }";
  document.head.appendChild(style);
  Explorer.registerView({ id: "languages", title: "Languages", nav: 65, render: listPage });
  Explorer.registerView({ id: "language", title: "Language", tab: "languages", render: detailPage });
})();
