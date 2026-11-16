// ---------- provenance: Lean sources and file bytes ----------
// When the page was generated with `--source-url` and `--source-rev`, it knows the GitHub
// repository, the commit, and the file of each module of the database (`SOURCE`). Problems and
// answers then link to their modules at that commit, and "view" fetches the file (from
// raw.githubusercontent.com, at most SOURCE_LIMIT bytes) and shows the declaration (its range
// from `decl_locations`, else found by a text search), highlighted and escaped. The link is
// evidence of where the declaration is written; that the kernel checked it is what the
// database's tier says, not what the source view shows.
const SOURCE = (() => {
  const s = JSON.parse(document.getElementById("source-meta").textContent || "null");
  if (!s || !/^https:\/\/github\.com\/[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(s.repo) || !/^[0-9a-f]{7,40}$/i.test(s.rev)) return null;
  return { repo: s.repo, rev: s.rev, modules: s.modules || {} };
})();
const SOURCE_LIMIT = 1 << 20;
// A repository file's blob page (for people) and raw URL (for fetching), at SOURCE's commit.
function repoFile(path) {
  if (!SOURCE || typeof path !== "string" || !path || /(^|\/)\.\.(\/|$)|^\//.test(path)) return null;
  const p = path.split("/").map(encodeURIComponent).join("/");
  const [, owner, repo] = SOURCE.repo.match(/^https:\/\/github\.com\/([^/]+)\/([^/]+)$/);
  return { path, blob: `${SOURCE.repo}/blob/${SOURCE.rev}/${p}`, raw: `https://raw.githubusercontent.com/${owner}/${repo}/${SOURCE.rev}/${p}` };
}
function moduleFile(module) { return SOURCE && module && Object.hasOwn(SOURCE.modules, module) ? repoFile(SOURCE.modules[module]) : null; }
// A link to `module`'s file, a button that shows `decl` in it and a link to its source page ("" when
// the page has no sources).
function sourceLink(module, decl) {
  const f = moduleFile(module);
  if (!f) return "";
  return `<a href="${esc(f.blob)}" target="_blank" rel="noopener noreferrer" title="${esc(f.path)} at ${esc(SOURCE.rev.slice(0, 12))}">source</a>` +
    (decl ? ` <button type="button" class="srcview" data-module="${esc(module)}" data-decl="${esc(decl)}" title="show the declaration in ${esc(f.path)}">view</button>` +
      ` <a class="srcpage" href="${esc(href("source", decl))}" title="the declaration's source on its own page">page</a>` : "");
}
// At most `limit` bytes of `url`: a Range request, and a reader that stops at the limit whatever
// the server answers. { bytes, total (the file's length, when known), complete }.
async function fetchBounded(url, limit) {
  const r = await fetch(url, { headers: { Range: `bytes=0-${limit - 1}` } });
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  const range = (r.headers.get("content-range") || "").match(/\/(\d+)$/);
  const enc = r.headers.get("content-encoding");
  let total = range ? Number(range[1]) : r.status === 200 && !enc && r.headers.get("content-length") ? Number(r.headers.get("content-length")) : null;
  const parts = [];
  let n = 0;
  const rd = r.body.getReader();
  while (n < limit) {
    const { done, value } = await rd.read();
    if (done) break;
    parts.push(value.subarray(0, limit - n)); n += Math.min(value.length, limit - n);
  }
  rd.cancel().catch(() => {});
  const bytes = new Uint8Array(n);
  let o = 0;
  for (const p of parts) { bytes.set(p, o); o += p.length; }
  if (total === null && n < limit) total = n;
  return { bytes, total, complete: total !== null && n === total };
}
// ---------- where a declaration is written, and the source view ----------
// Three concerns, kept apart so that each can be replaced alone:
//   * location (data): `declLocation(module, decl, text, ranges)` says where `decl` is written,
//       { module, path, startLine, endLine, selLine, selCol, selEndLine, selEndCol, exact, method, match }
//     from the database's `decl_locations` (Lean's `DeclarationRanges`: `method: "dump"`, exact),
//     else from a text search of the module's file (`LeanLocate`, `method: "text-search"`, not
//     exact: its extent is an estimate);
//   * tokens: `LeanTokenize.tokenizeLean` (explore/lean/tokenize.js), lexical and DOM-free;
//   * presentation: `LeanRender.renderLeanLines` (explore/lean/render.js) and `sourceHtml` below,
//     which frames the declaration's lines in the file. Hover types and go-to-definition, when
//     the database or a language server provides Lean's info trees, are marks given to
//     `renderLeanLines` (see there); neither the tokenizer nor the locator changes.
// The source view is the dialog of a "view" button, the `#/source/<decl>` page (views/source.js)
// and any `sourceBlock(module, decl)` a view puts in its HTML (filled once it is in the page).
const SOURCE_CONTEXT = 4, SOURCE_DECL_MAX = 400;
const RANGE_COLUMNS = ["line", "col", "end_line", "end_col", "sel_line", "sel_col", "sel_end_line", "sel_end_col"];
// The `decl_locations` row of `decl`, or null (no table, no row, or a row that is not a range).
async function declRanges(decl) {
  if (!decl || !tables.has("decl_locations")) return null;
  const r = (await tq("decl_locations", "SELECT * FROM decl_locations WHERE decl = ?", [decl]))[0];
  if (!r || typeof r.module !== "string" || !RANGE_COLUMNS.every((k) => Number.isInteger(r[k]) && r[k] >= 0)) return null;
  if (r.line < 1 || r.end_line < r.line || r.sel_line < r.line || r.sel_line > r.end_line) return null;
  return r;
}
// Where `decl` is written: Lean's ranges (`ranges`, a `declRanges` row) when there are some, else a
// text search of `text`, the file of `module` (`tokens`: its tokens, when already computed).
function declLocation(module, decl, text, ranges, tokens) {
  if (ranges) {
    const r = ranges;
    // Lean's end is the position after the last character: a range ending at column 0 ends on the line before.
    const endLine = r.end_col === 0 && r.end_line > r.line ? r.end_line - 1 : r.end_line;
    const loc = { module: r.module, path: (SOURCE && SOURCE.modules[r.module]) || null, startLine: r.line, endLine, selLine: r.sel_line, selCol: r.sel_col,
      selEndLine: r.sel_end_line, selEndCol: r.sel_end_col, exact: true, method: "dump", match: "name" };
    // A command that declares a constant (`silmaril instance N …`) may give the whole command as
    // the selection range: then the name is found by the text search, inside Lean's exact range.
    if ((r.sel_line !== r.sel_end_line || (r.sel_line === r.line && r.sel_col === r.col && r.sel_end_line === r.end_line)) && typeof text === "string") {
      const l = LeanLocate.locateLeanDecl(text, decl, { tokens });
      if (l && l.selLine >= loc.startLine && l.selLine <= loc.endLine) Object.assign(loc, { selLine: l.selLine, selCol: l.selCol, selEndLine: l.selLine, selEndCol: l.selEndCol });
    }
    return loc;
  }
  if (typeof text !== "string" || !decl) return null;
  const l = LeanLocate.locateLeanDecl(text, decl, { tokens });
  if (!l) return null;
  return { module, path: (SOURCE && SOURCE.modules[module]) || null, startLine: l.startLine, endLine: l.endLine, selLine: l.selLine, selCol: l.selCol,
    selEndLine: l.selLine, selEndCol: l.selEndCol, exact: false, method: "text-search", match: l.match, kind: l.kind, name: l.name };
}
// Files read for the source view, by raw URL (the last few: a file is often viewed twice).
const sourceFiles = new Map();
function readSource(raw) {
  if (!sourceFiles.has(raw)) {
    const p = fetchBounded(raw, SOURCE_LIMIT).then((r) => ({ text: new TextDecoder("utf-8").decode(r.bytes), complete: r.complete, bytes: r.bytes.length }));
    p.catch(() => sourceFiles.delete(raw));
    sourceFiles.set(raw, p);
    while (sourceFiles.size > 6) sourceFiles.delete(sourceFiles.keys().next().value);
  }
  return sourceFiles.get(raw);
}
// Everything the source view shows about `decl` in `module` (or in the module its
// `decl_locations` row names): { file, module, loc, text, tokens, complete, bytes, error }, or null
// when the page knows no file for it.
async function resolveSource(module, decl) {
  const ranges = await declRanges(decl);
  const mod = ranges && moduleFile(ranges.module) ? ranges.module : module;
  const file = moduleFile(mod);
  if (!file) return null;
  const res = { file, module: mod, loc: null, text: null, tokens: null, complete: false, bytes: 0, error: null };
  try {
    Object.assign(res, await readSource(file.raw));
    res.tokens = LeanTokenize.tokenizeLean(res.text);
  } catch (e) { res.error = String(e.message || e); }
  res.loc = declLocation(mod, decl, res.text, ranges && ranges.module === mod ? ranges : null, res.tokens);
  return res;
}
const srcPlural = (n, w) => `${n} ${w}${n === 1 ? "" : "s"}`;
const srcLines = (a, b) => (a === b ? `line ${a}` : `lines ${a}–${b}`);
// The source view's HTML for a `resolveSource` result: where the declaration is (a permalink to
// its lines at the commit), how it was found, and the file around it, highlighted, with the
// declaration's lines framed and its name marked.
let sourceViews = 0;   // ids of the source views on the page (labels and descriptions)
function sourceHtml(res, decl, pageLink) {
  const { file, loc } = res, rev = SOURCE.rev.slice(0, 12);
  const uid = "src-" + (++sourceViews);
  const blob = loc ? `${file.blob}#L${loc.startLine}${loc.endLine > loc.startLine ? "-L" + loc.endLine : ""}` : file.blob;
  let h = `<p class="src-where"><a class="src-permalink" href="${esc(blob)}" target="_blank" rel="noopener noreferrer" title="on GitHub, at commit ${esc(SOURCE.rev)}">` +
    `${esc(file.path)}${loc ? ", " + srcLines(loc.startLine, loc.endLine) : ""}</a> <span class="muted">at ${esc(rev)}</span> `;
  if (loc && loc.exact) h += '<span class="src-how src-exact" title="the range Lean recorded for the declaration (decl_locations)">exact: Lean\'s declaration range</span>';
  else if (loc) h += '<span class="src-how src-approx" title="the database records no range for this declaration">approximate: found by a text search</span>';
  h += decl && pageLink !== false ? ` · <a href="${esc(href("source", decl))}">source page</a></p>` : "</p>";
  const name = `<code>${esc(decl || "")}</code>`;
  if (loc && !loc.exact) {
    const how = { name: "its full name", alias: "a name it answers", suffix: "the end of its name",
      last: `the last component of its name only (<code>${esc(String(decl).split(".").pop())}</code>): check that it is the right one` }[loc.match] || "its name";
    h += `<p class="muted">Found by ${how}, as <code>${esc(loc.kind || "")} ${esc(loc.name || "")}</code>; the end of the declaration is estimated (up to the next command). ` +
      `The database records the declaration ${name} in module <code>${esc(res.module)}</code>.</p>`;
  }
  if (res.error) {
    return h + `<p class="err">could not read ${esc(file.raw)}: ${esc(res.error)}</p><p><a href="${esc(blob)}" target="_blank" rel="noopener noreferrer">open it on GitHub</a></p>`;
  }
  const lines = res.text.split("\n");
  if (!loc) {
    h += `<p class="muted">No declaration of ${name} was found in this file by a text search${res.complete ? "" : ` (only its first ${res.bytes} bytes were read)`}; the start of the file:</p>`;
    return h + srcCodeBlock(res, 1, Math.min(lines.length, 40), null, uid, `the start of ${file.path}`);
  }
  if (loc.startLine > lines.length) {
    return h + `<p class="muted">The declaration starts after the first ${res.bytes} bytes of the file, which is all that is read here: open it on GitHub.</p>`;
  }
  const last = Math.min(loc.endLine, lines.length, loc.startLine + SOURCE_DECL_MAX - 1);
  const from = Math.max(1, loc.startLine - SOURCE_CONTEXT), to = Math.min(lines.length, last + SOURCE_CONTEXT);
  const cut = loc.endLine > last ? ` Only its first ${srcPlural(last - loc.startLine + 1, "line")} are shown here; the rest is on GitHub.` : "";
  h += srcCodeBlock(res, from, to, Object.assign({}, loc, { last }), uid, `${file.path}, ${srcLines(from, to)}`);
  h += `<p class="src-note" id="${uid}-note">${esc(srcLines(loc.startLine, loc.endLine).replace(/^l/, "L"))} (framed; the name is marked on line ${loc.selLine}): ` +
    `the whole declaration ${name} (statement and proof)${loc.exact ? "" : ", as far as a text search can tell"}.${cut}</p>`;
  return h;
}
// The numbered, highlighted lines `from..to` of the file, with `loc`'s lines `startLine..last` framed.
function srcCodeBlock(res, from, to, loc, uid, label) {
  const marks = loc && loc.selEndLine === loc.selLine && loc.selEndCol > loc.selCol
    ? [{ line: loc.selLine, col: loc.selCol, endCol: loc.selEndCol, cls: "lean-sel", title: "the declaration's name" }] : [];
  const html = LeanRender.renderLeanLines(res.tokens, from, to, { marks });
  const w = String(to).length;
  const row = (l) => `<span class="sl${loc && l === loc.selLine ? " sl-sel" : ""}" data-line="${l}"><span class="ln">${String(l).padStart(w)}</span> ${html[l - from]}</span>`;
  let body = "";
  for (let l = from; l <= to; l++) {
    if (loc && l === loc.startLine) body += `<span class="src-decl" role="group" aria-current="location" aria-label="the declaration, ${esc(srcLines(loc.startLine, loc.endLine))}">`;
    body += row(l);
    if (loc && l === loc.last) body += "</span>";
  }
  return `<pre class="code lean" tabindex="0" role="region" aria-label="Lean source: ${esc(label)}"${loc ? ` aria-describedby="${uid}-note"` : ""}>${body}</pre>`;
}
// Once the view is in the page: scroll its code so that the declaration is in sight.
function revealDecl(root) {
  for (const pre of root.querySelectorAll("pre.lean")) {
    const g = pre.querySelector(".src-decl");
    if (g) pre.scrollTop = Math.max(0, g.offsetTop - 2 * (parseFloat(getComputedStyle(pre).lineHeight) || 16));
  }
}
// Fills `el` with the source view of `decl` in `module`.
async function fillSource(el, module, decl, pageLink) {
  try {
    const res = await resolveSource(module, decl);
    if (!el.isConnected) return;
    el.innerHTML = res ? sourceHtml(res, decl, pageLink) : `<p class="muted">The page knows no source file for module <code>${esc(module || "?")}</code>.</p>`;
    revealDecl(el);
  } catch (e) {
    if (e instanceof Superseded) return;
    if (el.isConnected) el.innerHTML = `<p class="err">${esc(e.message || e)}</p>`;
  }
}
// The source view of `decl` as HTML for any view, filled once it is in the page; "" when the page
// has no sources for `module` (and no `decl_locations` table that could name another module).
// `opts.pageLink: false` leaves out the link to the `#/source/<decl>` page.
function sourceBlock(module, decl, opts) {
  if (!SOURCE || (!moduleFile(module) && !tables.has("decl_locations"))) return "";
  return `<div class="lean-src" data-module="${esc(module || "")}" data-decl="${esc(decl || "")}"${opts && opts.pageLink === false ? ' data-nopage="1"' : ""} data-pending="1"><p class="muted">reading the Lean source…</p></div>`;
}
new MutationObserver(() => {
  for (const el of document.querySelectorAll(".lean-src[data-pending]")) {
    el.removeAttribute("data-pending");
    fillSource(el, el.dataset.module, el.dataset.decl, !el.dataset.nopage);
  }
}).observe(document.documentElement, { childList: true, subtree: true });
async function showSource(module, decl) {
  if (!SOURCE || (!moduleFile(module) && !tables.has("decl_locations"))) return;
  const d = dialog({ title: decl || module, body: '<div class="lean-src"><p class="muted">reading the Lean source…</p></div>' });
  d.el.classList.add("dlg-wide");
  await fillSource(d.el.querySelector(".lean-src"), module, decl);
}
// A dialog with the first VIEWER_LIMIT bytes of `url` in the byte viewer; when the whole file was
// read and `sha256` is given, whether the bytes match it.
async function showBytes(url, meta) {
  const d = dialog({ title: meta.name || url, body: `<p class="muted">reading…</p>` });
  const body = d.el.querySelector(".dlg-body");
  try {
    const r = await fetchBounded(url, meta.limit || VIEWER_LIMIT);
    let check = "";
    if (meta.sha256 && r.complete) {
      const sha = await sha256Hex(r.bytes);
      check = sha === meta.sha256 ? '<p>SHA-256 of these bytes matches the registry.</p>'
        : `<p class="err">SHA-256 of these bytes (${esc(sha || "?")}) differs from the registry's (${esc(meta.sha256)}).</p>`;
    } else if (meta.sha256) check = '<p class="muted">Not the whole file: its SHA-256 is not checked here.</p>';
    const v = viewer(r.bytes, Object.assign({}, meta, { total: r.total == null ? r.bytes.length : r.total }));
    body.innerHTML = `<p class="muted">${esc(url)}</p>` + check + v.html;
    v.init(body);
  } catch (e) {
    body.innerHTML = `<p class="err">could not read ${esc(url)}: ${esc(e.message || e)}</p>`;
  }
}
// Buttons anywhere in the page: [class=srcview] shows a declaration, [data-bytes] a file.
document.addEventListener("click", (e) => {
  const b = e.target.closest && e.target.closest("button.srcview, button[data-bytes]");
  if (!b) return;
  if (b.classList.contains("srcview")) showSource(b.dataset.module, b.dataset.decl);
  else showBytes(b.dataset.bytes, { name: b.dataset.name, sha256: b.dataset.sha256 || null, lang: b.dataset.lang || null });
});
