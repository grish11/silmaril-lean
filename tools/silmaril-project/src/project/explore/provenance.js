// ---------- provenance: Lean sources and file bytes ----------
// When the page was generated with `--source-url` and `--source-rev`, it knows the GitHub
// repository, the commit, and the file of each module of the database (`SOURCE`). Problems and
// answers then link to their modules at that commit, and "view" fetches the file (from
// raw.githubusercontent.com, at most SOURCE_LIMIT bytes) and shows the declaration found by a text
// search, escaped. The link is evidence of where the declaration is written; that the kernel
// checked it is what the database's tier says, not what the source view shows.
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
// A link to `module`'s file and a button that shows `decl` in it ("" when the page has no sources).
function sourceLink(module, decl) {
  const f = moduleFile(module);
  if (!f) return "";
  return `<a href="${esc(f.blob)}" target="_blank" rel="noopener noreferrer" title="${esc(f.path)} at ${esc(SOURCE.rev.slice(0, 12))}">source</a>` +
    (decl ? ` <button type="button" class="srcview" data-module="${esc(module)}" data-decl="${esc(decl)}">view</button>` : "");
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
// The line (1-based) where `decl`'s last name component is declared, by a text search.
function findDecl(text, decl) {
  const last = String(decl).split(".").pop();
  if (!last) return 0;
  const name = last.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const re = new RegExp(`^\\s*(?:@\\[.*?\\]\\s*)?(?:(?:public|private|protected|noncomputable|partial|unsafe|nonrec|meta)\\s+)*` +
    `(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom|opaque)\\s+(?:[\\w.']*\\.)?${name}(?![\\w'])`);
  const lines = text.split("\n");
  for (let i = 0; i < lines.length; i++) if (re.test(lines[i])) return i + 1;
  return 0;
}
function numbered(lines, from, mark) {
  const w = String(from + lines.length).length;
  return lines.map((l, i) => { const t = `<span class="ln">${String(from + i).padStart(w)}</span> ${esc(l)}`;
    return from + i === mark ? `<mark>${t}</mark>` : t; }).join("\n");
}
async function showSource(module, decl) {
  const f = moduleFile(module);
  if (!f) return;
  const d = dialog({ title: decl || module, body: `<p class="muted">reading ${esc(f.path)}…</p>` });
  const body = d.el.querySelector(".dlg-body");
  try {
    const r = await fetchBounded(f.raw, SOURCE_LIMIT);
    const text = new TextDecoder("utf-8").decode(r.bytes);
    const line = decl ? findDecl(text, decl) : 0;
    const lines = text.split("\n");
    const from = Math.max(1, (line || 1) - 2), to = Math.min(lines.length, (line || 1) + 45);
    body.innerHTML = `<p><a href="${esc(f.blob)}${line ? "#L" + line : ""}" target="_blank" rel="noopener noreferrer">${esc(f.path)}${line ? ":" + line : ""}</a> ` +
      `<span class="muted">at ${esc(SOURCE.rev.slice(0, 12))}</span></p>` +
      `<p class="muted">${line ? `The declaration was found by a text search for <code>${esc(String(decl).split(".").pop())}</code> after a declaration keyword; ` +
        `the kernel-checked declaration is <code>${esc(decl)}</code> in module <code>${esc(module)}</code>.`
        : `No line declaring <code>${esc(String(decl || "").split(".").pop())}</code> was found by a text search (it may be generated by a command); the start of the file:`}` +
      `${r.complete ? "" : ` Only the first ${r.bytes.length} bytes were read.`}</p>` +
      `<pre class="code" tabindex="0">${numbered(lines.slice(from - 1, to), from, line)}</pre>`;
  } catch (e) {
    body.innerHTML = `<p class="err">could not read ${esc(f.raw)}: ${esc(e.message || e)}</p><p><a href="${esc(f.blob)}" target="_blank" rel="noopener noreferrer">open it on GitHub</a></p>`;
  }
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
