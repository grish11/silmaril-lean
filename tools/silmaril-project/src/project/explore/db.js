// ---------- loading ----------
function isSqlite(buf) { return buf.length >= 16 && new TextDecoder().decode(buf.slice(0, 15)) === "SQLite format 3"; }
// A same-origin blob: URL for a CDN file checked against its SRI hash (workers must be same-origin).
async function sriBlobUrl(url, integrity, type) {
  const r = await fetch(url, { integrity, mode: "cors" });
  if (!r.ok) throw new Error(`${url}: HTTP ${r.status}`);
  return URL.createObjectURL(new Blob([await r.arrayBuffer()], { type }));
}
let sqlJs = null;
function loadSqlJs() {
  return sqlJs || (sqlJs = (async () => {
    const wasm = await sriBlobUrl(SQLJS + "sql-wasm.wasm", SQLJS_WASM_SRI, "application/wasm");
    return initSqlJs({ locateFile: () => wasm });
  })());
}
// A backend: query(sql, params) -> rows as objects; exec(sql) -> [{columns, values}]; stats().
async function wholeBackend(bytes, mode) {
  const SQL = await loadSqlJs();
  const d = new SQL.Database(bytes);
  return {
    mode, size: bytes.length,
    async query(sql, params) {
      const st = d.prepare(sql);
      try { st.bind(params); const out = []; while (st.step()) out.push(st.getAsObject()); return out; }
      finally { st.free(); }
    },
    async exec(sql) { return d.exec(sql); },
    async stats() { return { totalBytes: bytes.length, totalFetchedBytes: bytes.length, totalRequests: mode === "local file" ? 0 : 1 }; },
    close() { d.close(); },
  };
}
// Lazy reads with sql.js-httpvfs. The file length and a version tag come from our own Range
// probe, not from the library's HEAD request: some static hosts (GitHub Pages) gzip HEAD and
// whole-file responses, which hides the real length, while they answer Range requests with the
// identity bytes and `Content-Range: bytes a-b/<length>`. The single-chunk "chunked" mode lets us
// give that length; the version tag (`v=`, from the strong ETag or Last-Modified, and the length)
// is part of every range URL, so the browser's HTTP cache can reuse pages across reloads of one
// version and can never mix pages of two versions.
async function lazyBackend(url, pageSize, length, tag) {
  if (typeof createDbWorker !== "function") throw new Error("sql.js-httpvfs did not load");
  const [worker, wasm] = await Promise.all([
    sriBlobUrl(HTTPVFS + "sqlite.worker.js", HTTPVFS_WORKER_SRI, "text/javascript"),
    sriBlobUrl(HTTPVFS + "sql-wasm.wasm", HTTPVFS_WASM_SRI, "application/wasm")]);
  const prefix = url + (url.includes("?") ? "&" : "?") + "v=" + encodeURIComponent(tag) + "&part=";
  const w = await createDbWorker([{ from: "inline", config: { serverMode: "chunked", urlPrefix: prefix,
    serverChunkSize: length, databaseLengthBytes: length, suffixLength: 1, requestChunkSize: pageSize } }], worker, wasm);
  return {
    mode: `lazy (HTTP Range, ${pageSize} B pages, version ${tag})`, pageSize, size: length, tag,
    query: (sql, params) => w.db.query(sql, params),
    exec: (sql) => w.db.exec(sql),
    stats: () => w.worker.getStats(),
    close() { /* the worker stays until the page closes */ },
  };
}
// The service worker (explore-sw.js, written next to the page) caches lazily read pages across
// reloads. Without it (file://, a browser without service workers, or a host that does not serve
// the file) the page works the same and only the in-session cache of sql.js-httpvfs applies.
async function registerPageCache() {
  if (!("serviceWorker" in navigator) || !/^https?:$/.test(location.protocol) || PARAMS.get("cache") === "off") return false;
  try {
    await navigator.serviceWorker.register("explore-sw.js");
    await navigator.serviceWorker.ready;
    // a first registration controls this page once `clients.claim()` has run
    if (!navigator.serviceWorker.controller) await new Promise((res) => {
      navigator.serviceWorker.addEventListener("controllerchange", res, { once: true });
      setTimeout(res, 1500);
    });
    return !!navigator.serviceWorker.controller;
  } catch (e) { return false; }
}
async function sha256Hex(bytes) {
  if (!crypto.subtle) return null;
  const d = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  return [...d].map((b) => b.toString(16).padStart(2, "0")).join("");
}
// What we can say about the bytes against the page's DB_META (same URL only).
function metaNote(u, size, sha) {
  if (!DB_META || DB_META.url !== u) return "";
  if (size !== undefined && size !== DB_META.size) return "; the page was generated for another version of the database";
  if (sha) return sha === DB_META.sha256 ? "; SHA-256 verified" : "; SHA-256 differs from the page's";
  return "";
}
// Open `u` over http(s): probe with a Range request for the 100-byte header. 206 with identity
// bytes and a `Content-Range` total -> lazy; otherwise download the whole file (and check its
// SHA-256 against the page's when it has one).
async function openUrl(u) {
  const url = new URL(u, location.href).href;
  let r;
  try { r = await fetch(url, { headers: { Range: "bytes=0-99" }, cache: "no-store" }); }
  catch (e) { throw new Error("could not fetch (" + e.message + ")"); }
  if (!r.ok) throw new Error("HTTP " + r.status);
  const enc = r.headers.get("content-encoding");
  const total = Number(((r.headers.get("content-range") || "").match(/\/(\d+)$/) || [])[1]);
  const ranged = r.status === 206 && (!enc || enc === "identity");
  let note = "";
  if (ranged) {
    const head = new Uint8Array(await r.arrayBuffer());
    if (!isSqlite(head)) throw new Error("not a SQLite database");
    const ps = (head[16] << 8) | head[17];
    const etag = r.headers.get("etag");
    const tag = ((etag && !etag.startsWith("W/") ? etag : r.headers.get("last-modified")) || "").replace(/[^A-Za-z0-9._-]/g, "") + "-" + total;
    if (PARAMS.get("load") !== "full") {
      const cached = await registerPageCache();
      if (!total) note = " (lazy loading needs the file length; the server sent no Content-Range total)";
      else {
        try {
          const b = await lazyBackend(url, ps === 1 ? 65536 : ps, total, tag);
          b.mode += (cached ? "; pages cached across reloads" : "") + metaNote(u, total);
          return b;
        } catch (e) { note = ` (lazy loading failed: ${e.message || e})`; }
      }
    }
    r = await fetch(url, { cache: "no-store" });
    if (!r.ok) throw new Error("HTTP " + r.status);
  }
  const bytes = new Uint8Array(await r.arrayBuffer());
  if (!isSqlite(bytes)) throw new Error("not a SQLite database");
  const sha = await sha256Hex(bytes);
  return wholeBackend(bytes, (ranged ? "whole file" : "whole file (the server ignored Range)") + note + metaNote(u, bytes.length, sha));
}
function pickHelp(why) {
  const def = DB_URLS[0] || "project.sqlite";
  return `<div class="pick"><h2>Choose the database</h2>${why}
    <p><label>Open a project.sqlite <input type="file" class="dbfile" accept=".sqlite,.sqlite3,.db"></label>, or drop it on this page.
    <code>sil project sqlite</code> writes it to <code>${esc(def)}</code> (relative to this page).
    The file is read in the browser; nothing is uploaded.</p>
    <p>To have the page open it by itself, serve the project directory over HTTP, preferably with a
    server that supports Range requests so that only the pages a view needs are fetched, e.g.
    <code>npx http-server -p 8080 .lake/silmaril</code> in the project directory (by default the
    page and the database are both there), then open <code>http://localhost:8080/explore.html</code>.
    Another file: add <code>?db=&lt;url&gt;</code>.</p></div>`;
}
// ---------- the source: which database is open ----------
// One database is open at a time. Opening another (a URL, a chosen or dropped file) takes a new
// `openTok`: an attempt that finishes after a later one started is closed and dropped, so a slow
// download can never replace the file the reader chose since.
let openTok = 0;
const source = { label: null, mode: null, schema: null, problem: null };
function shortMode(mode) {
  return !mode ? "" : /^lazy/.test(mode) ? "lazy" : /^local/.test(mode) ? "local file" : "whole file";
}
function renderSource() {
  const el = $("#source");
  const name = source.label ? source.label.replace(/[?#].*$/, "").split("/").pop() || source.label : "no database";
  const warn = source.problem || (source.schema && source.schema !== SCHEMA);
  el.innerHTML = `<span class="src-name">${esc(name)}</span>` + (source.mode ? ` <span class="muted">${esc(shortMode(source.mode))}</span>` : "") +
    (warn ? ' <b class="src-warn" aria-hidden="true">!</b>' : "");
  el.setAttribute("aria-label", `Database: ${source.label || "none"}${source.mode ? ", " + source.mode : ""}${warn ? ", needs attention" : ""}. Show details or open another.`);
  el.title = "the database this page reads: details, or open another";
}
async function sourceDialog() {
  const s = be ? await be.stats().catch(() => null) : null;
  const row = (k, v) => v ? `<dt>${esc(k)}</dt><dd>${v}</dd>` : "";
  const body = (source.problem ? `<p class="err" role="alert">${esc(source.problem)}</p>` : "") +
    "<dl>" + row("source", source.label ? `<code>${esc(source.label)}</code>` : "none") +
    row("read", source.mode && esc(source.mode)) +
    row("schema", source.schema && `<code>${esc(source.schema)}</code>` + (source.schema === SCHEMA ? "" : ` <span class="err">this page expects ${esc(SCHEMA)}</span>`)) +
    row("transferred", s && (be.mode === "local file" ? `${esc(kB(s.totalBytes))} in memory` :
      `${esc(kB(s.totalFetchedBytes))} of ${esc(kB(s.totalBytes))}${s.totalRequests ? ` in ${s.totalRequests} requests` : ""}`)) + "</dl>" +
    '<h3>Open another database</h3><p><label>file <input type="file" class="dbfile" accept=".sqlite,.sqlite3,.db"></label> ' +
    '<span class="muted">read in the browser; nothing is uploaded</span></p>' +
    '<form class="dburl"><label>URL <input type="text" name="u" size="40" placeholder="project.sqlite or https://…"></label> <button type="submit">Open</button></form>' +
    (DB_URLS.length ? `<p class="muted">this page's default: <code>${esc(DB_URLS[0])}</code></p>` : "");
  const d = dialog({ title: "Database", body });
  wireFilePickers(d.el, d.close);
  d.el.querySelector("form.dburl").addEventListener("submit", (e) => {
    e.preventDefault();
    const u = e.target.u.value.trim();
    if (u) { d.close(); openSource(u, () => openUrl(u)); }
  });
}
function wireFilePickers(root, done) {
  for (const i of root.querySelectorAll("input.dbfile")) i.addEventListener("change", (e) => {
    const f = e.target.files[0];
    if (f) { if (done) done(); openFile(f); }
  });
}
// Open what `make()` returns under `label`; false when a later attempt superseded this one.
async function openSource(label, make) {
  const tok = ++openTok;
  $("#main").innerHTML = `<div id="msg">Opening ${esc(label)}…</div>`;
  try {
    const b = await make();
    if (tok !== openTok) { if (b.close) b.close(); return false; }
    await useDb(b, label);
    return true;
  } catch (e) {
    if (tok !== openTok || e instanceof Superseded) return false;
    $("#main").innerHTML = `<div id="msg">${pickHelp(`<p class="err">could not open ${esc(label)}: ${esc(e.message || e)}</p>`)}</div>`;
    wireFilePickers($("#main"));
    return false;
  }
}
async function boot() {
  renderNav();
  renderSource();
  const urls = [...new Set([PARAMS.get("db"), ...DB_URLS].filter(Boolean))];
  if (location.protocol === "file:") {
    $("#main").innerHTML = `<div id="msg">${pickHelp(`<p>This page was opened from a file (<code>file://</code>),
      where browsers block it from reading other files, including ${urls.map((u) => `<code>${esc(u)}</code>`).join(", ")}.</p>`)}</div>`;
    wireFilePickers($("#main"));
    return;
  }
  const tok = ++openTok, tried = [];
  for (const u of urls) {
    $("#msg") && ($("#msg").textContent = `Opening ${u}…`);
    let b;
    try { b = await openUrl(u); }
    catch (e) { tried.push(`<li><code>${esc(u)}</code>: ${esc(e.message || e)}</li>`); continue; }
    if (tok !== openTok) { if (b.close) b.close(); return; }   // the reader chose a file meanwhile
    try { return await useDb(b, u); } catch (e) { if (e instanceof Superseded) return; throw e; }
  }
  if (tok !== openTok) return;
  $("#main").innerHTML = `<div id="msg">${pickHelp(`<p>No database could be opened from:</p><ul>${tried.join("")}</ul>`)}</div>`;
  wireFilePickers($("#main"));
}
async function useDb(b, label) {
  if (be && be.close) try { be.close(); } catch (e) { /* ignore */ }
  be = b;
  disposeRoute();
  routeTok++;   // whatever the old database's route still awaits is superseded
  known = Object.fromEntries(KINDS.map((k) => [k, new Map()]));
  verdictOf = new Map(); summaryOf = new Map(); statusOf = new Map();
  const ts = await q("SELECT name FROM sqlite_master WHERE type IN ('table', 'view')");
  const ix = await q("SELECT name FROM sqlite_master WHERE type = 'index'");
  tables = new Set(ts.map((r) => r.name));
  indexes = new Set(ix.map((r) => r.name));
  let schema = "?";
  if (tables.has("meta")) schema = ((await q("SELECT value FROM meta WHERE key = 'schema'"))[0] || {}).value || "?";
  Object.assign(source, { label, mode: b.mode, schema, problem: null });
  renderSource();
  Object.assign(window.explore, { ready: true, mode: b.mode, source: label, opened: (window.explore.opened || 0) + 1 });
  await route();
}
async function updateStats() {
  if (!be) return;
  const s = await be.stats();
  if (s) {
    $("#stats").textContent = be.mode === "local file" ? `${kB(s.totalBytes)} in memory`
      : `read ${kB(s.totalFetchedBytes)} of ${kB(s.totalBytes)}`;
    window.explore.stats = s;
  }
}
function openFile(f) {
  return openSource(f.name, async () => {
    const bytes = new Uint8Array(await f.arrayBuffer());
    if (!isSqlite(bytes)) throw new Error("not a SQLite database (run `sil project sqlite` and choose its .sqlite file)");
    return wholeBackend(bytes, "local file");
  });
}
$("#source").addEventListener("click", () => { sourceDialog(); });
document.addEventListener("dragover", (e) => { e.preventDefault(); $("#drop").style.display = "flex"; });
document.addEventListener("dragleave", (e) => { if (!e.relatedTarget) $("#drop").style.display = "none"; });
document.addEventListener("drop", (e) => {
  e.preventDefault(); $("#drop").style.display = "none";
  if (e.dataTransfer.files[0]) openFile(e.dataTransfer.files[0]);
});

