// ---------- loading ----------
function isSqlite(buf) { return buf.length >= 16 && new TextDecoder().decode(buf.slice(0, 15)) === "SQLite format 3"; }
// A same-origin blob: URL for a CDN file checked against its SRI hash (workers must be same-origin).
// `prefix`, when given, is prepended to the checked bytes (the worker's snapshot guard).
async function sriBlobUrl(url, integrity, type, prefix) {
  const r = await fetch(url, { integrity, mode: "cors" });
  if (!r.ok) throw new Error(`${url}: HTTP ${r.status}`);
  return URL.createObjectURL(new Blob([prefix || "", await r.arrayBuffer()], { type }));
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
// ---------- one snapshot per lazily read database ----------
// A lazily read database is read one page at a time, for as long as the page is open. If the
// file on the server is replaced meanwhile (`sil project sqlite` rewrites it, a new deploy), a
// later read would get a page of the new file under the old version's URL, and SQLite would see
// pages of two different files: "database disk image is malformed", or silently wrong rows.
// So every range read is checked, in the worker, against the version the database was opened
// at (`versionOf` its probe): the response must be a 206 of exactly the requested bytes, of a
// file of the same length and the same validator (strong ETag, else Last-Modified). A read that
// fails the check fails its query (it is never retried), the database is marked as changed, and
// the page offers to open the new version. A malformed database whose version has not changed
// is reported as damage of the file itself, not as a version change.
// Lazy reads are used only when the server names its file by a strong ETag (see `openUrl`);
// GitHub Pages does. Otherwise the file is read whole, in one response.
const SNAPSHOT_CHANNEL = "silmaril-explore-snapshot";
function versionOf(etag, lastModified, total) {
  return ((etag && !etag.startsWith("W/") ? etag : lastModified) || "").replace(/[^A-Za-z0-9._-]/g, "") + "-" + total;
}
// Runs in the worker, before sql.js-httpvfs: wraps its synchronous XMLHttpRequests. Only reads
// (GET) of version-tagged URLs (`?v=<version>&part=…`) are checked, and they must be ranges. Once one fails, every later read
// of that version fails too, so nothing read after a change is ever used.
function snapshotGuard(versionOf, channel) {
  const X = self.XMLHttpRequest.prototype, open = X.open, setHeader = X.setRequestHeader, send = X.send;
  const broken = new Map();   // version -> why
  const fail = (v, why, now) => {
    if (!broken.has(v)) {
      broken.set(v, why);
      try { const c = new BroadcastChannel(channel); c.postMessage({ v, why, now: now || null }); c.close(); } catch (e) { /* no channel */ }
    }
    throw new Error("silmaril snapshot: " + why);
  };
  X.open = function (method, url) { this.silGet = /^get$/i.test(method); this.silUrl = String(url); this.silRange = null; return open.apply(this, arguments); };
  X.setRequestHeader = function (k, val) { if (/^range$/i.test(k)) this.silRange = String(val); return setHeader.apply(this, arguments); };
  X.send = function () {
    let v = null;
    try { v = new URL(this.silUrl, self.location.href).searchParams.get("v"); } catch (e) { /* not a URL we tag */ }
    // the library's HEAD (it asks for the length, which it was given) reads no bytes
    if (v === null || !this.silGet) return send.apply(this, arguments);
    if (broken.has(v)) fail(v, broken.get(v));
    const out = send.apply(this, arguments);
    const total = v.slice(v.lastIndexOf("-") + 1);
    const want = /^bytes=(\d+)-(\d+)$/.exec(this.silRange || "");
    const got = /^bytes (\d+)-(\d+)\/(\d+)$/.exec(this.getResponseHeader("content-range") || "");
    const enc = this.getResponseHeader("content-encoding");
    if (this.status !== 206 || !got || (enc && enc !== "identity")) fail(v, `a range read was answered with HTTP ${this.status}` +
      (got ? "" : " and no byte range") + (enc && enc !== "identity" ? `, ${enc}-encoded` : ""));
    const now = versionOf(this.getResponseHeader("etag"), this.getResponseHeader("last-modified"), got[3]);
    if (got[3] !== total) fail(v, `the file is now ${got[3]} bytes long, not ${total}`, now);
    if (now !== v) fail(v, `the server now serves version ${now}`, now);
    if (want && (got[1] !== want[1] || got[2] !== want[2])) fail(v, `bytes ${got[1]}-${got[2]} came back for ${want[1]}-${want[2]}`);
    const n = this.response && this.response.byteLength;
    if (want && n !== +want[2] - +want[1] + 1) fail(v, `${n} bytes came back for a range of ${+want[2] - +want[1] + 1}`);
    return out;
  };
}
// The database changed on the server after it was opened: `was` and `now` are versions.
class SourceChanged extends Error {
  constructor(url, was, now, why) {
    super(`${url} changed on the server after this page opened it` + (now ? ` (version ${was}; the server now has ${now})` : ` (${why || "version " + was})`) +
      ". Nothing read since was used.");
    this.name = "SourceChanged"; Object.assign(this, { url, was, now, why });
  }
}
// The version the server has now, from a fresh probe (null when it cannot be read).
async function probeVersion(url) {
  try {
    const r = await fetch(url, { headers: { Range: "bytes=0-99" }, cache: "no-store" });
    const total = Number(((r.headers.get("content-range") || "").match(/\/(\d+)$/) || [])[1]);
    return r.status === 206 && total ? versionOf(r.headers.get("etag"), r.headers.get("last-modified"), total) : null;
  } catch (e) { return null; }
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
  const guard = `(${snapshotGuard})(${versionOf}, ${JSON.stringify(SNAPSHOT_CHANNEL)});\n`;
  const [worker, wasm] = await Promise.all([
    sriBlobUrl(HTTPVFS + "sqlite.worker.js", HTTPVFS_WORKER_SRI, "text/javascript", guard),
    sriBlobUrl(HTTPVFS + "sql-wasm.wasm", HTTPVFS_WASM_SRI, "application/wasm")]);
  const prefix = url + (url.includes("?") ? "&" : "?") + "v=" + encodeURIComponent(tag) + "&part=";
  const w = await createDbWorker([{ from: "inline", config: { serverMode: "chunked", urlPrefix: prefix,
    serverChunkSize: length, databaseLengthBytes: length, suffixLength: 1, requestChunkSize: pageSize } }], worker, wasm);
  // What the worker's guard reported for this version (it may arrive after the failed query).
  let changed = null, guardSaid = null;
  const ch = typeof BroadcastChannel === "function" ? new BroadcastChannel(SNAPSHOT_CHANNEL) : null;
  if (ch) ch.onmessage = (e) => { if (e.data && e.data.v === tag && !guardSaid) guardSaid = e.data; };
  // A failed query: a changed source (the guard said so, or the server's version differs now),
  // or else the error as SQLite gave it, with what the version check adds to it.
  const explain = async (e) => {
    if (changed) return changed;
    const now = await probeVersion(url);
    if (!guardSaid) await sleep(50);
    if ((now && now !== tag) || guardSaid) {
      changed = new SourceChanged(url, tag, now && now !== tag ? now : guardSaid && guardSaid.now, guardSaid && guardSaid.why);
      noteChanged(changed);
      return changed;
    }
    if (/malformed|not a database|corrupt/i.test(String(e && e.message)) && now === tag) {
      return new Error(`${e.message}. The server still serves the version this page opened (${tag}), and every page read ` +
        "was checked against it, so this is not a mix of two versions: the file itself is damaged, or not a database this page can read " +
        "(check it with `sqlite3 <file> 'PRAGMA integrity_check'`).");
    }
    return e;
  };
  const run = async (f) => {
    if (changed) throw changed;
    try { return await f(); } catch (e) { throw await explain(e); }
  };
  return {
    mode: `lazy (HTTP Range, ${pageSize} B pages, version ${tag})`, pageSize, size: length, tag,
    query: (sql, params) => run(() => w.db.query(sql, params)),
    exec: (sql) => run(() => w.db.exec(sql)),
    stats: () => w.worker.getStats(),
    changed: () => changed,
    close() { if (ch) ch.close(); /* the worker stays until the page closes */ },
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
// Reading lazily keeps one snapshot only when every range response names its file by a strong
// ETag (see the snapshot guard above): a Last-Modified date has a resolution of one second and a
// weak ETag (`W/…`) does not promise the same bytes, so a file replaced by another of the same
// size within that second would pass for the same version. Without a strong ETag the page reads
// the whole file in one response instead (one response is one file), up to WHOLE_LIMIT bytes;
// a larger file is read whole only when the reader asks (`opts.whole`, or `?load=full`).
// `?whole-limit=<bytes>` may only lower it (for tests and small devices).
const WHOLE_LIMIT = Math.min(256 * 1024 * 1024, Number(PARAMS.get("whole-limit")) || Infinity);
class TooLarge extends Error {
  constructor(url, total, why) {
    super(`${url} is ${total ? kB(total) : "of unknown size"}; ${why}, so it would be read whole into memory`);
    this.name = "TooLarge"; Object.assign(this, { url, total });
  }
}
// The body of `r`, failing beyond `limit` bytes (whatever the headers said).
async function readCapped(r, limit, url, why) {
  const parts = []; let n = 0;
  const rd = r.body.getReader();
  for (;;) {
    const { done, value } = await rd.read();
    if (done) break;
    n += value.length;
    if (n > limit) { rd.cancel().catch(() => {}); throw new TooLarge(url, null, why); }
    parts.push(value);
  }
  const out = new Uint8Array(n); let o = 0;
  for (const p of parts) { out.set(p, o); o += p.length; }
  return out;
}
// Open `u` over http(s): probe with a Range request for the 100-byte header. 206 with identity
// bytes, a `Content-Range` total and a strong ETag -> lazy; otherwise read the whole file (and
// check its SHA-256 against the page's when it has one).
async function openUrl(u, opts) {
  const url = new URL(u, location.href).href;
  const whole = PARAMS.get("load") === "full" || !!(opts && opts.whole);
  let r;
  try { r = await fetch(url, { headers: { Range: "bytes=0-99" }, cache: "no-store" }); }
  catch (e) { throw new Error("could not fetch (" + e.message + ")"); }
  if (!r.ok) throw new Error("HTTP " + r.status);
  const enc = r.headers.get("content-encoding");
  const total = Number(((r.headers.get("content-range") || "").match(/\/(\d+)$/) || [])[1]);
  const ranged = r.status === 206 && (!enc || enc === "identity");
  const etag = r.headers.get("etag");
  const strong = !!etag && !etag.startsWith("W/");
  let note = "", why = "";
  if (ranged) {
    const head = new Uint8Array(await r.arrayBuffer());
    if (!isSqlite(head)) throw new Error("not a SQLite database");
    const ps = (head[16] << 8) | head[17];
    if (!whole) {
      if (!total) why = "the server sent no Content-Range total";
      else if (!strong) why = `the server sent no strong ETag (${etag ? "a weak one" : r.headers.get("last-modified") ? "only Last-Modified" : "no validator"}), which lazy reads need to stay on one version`;
      else {
        const cached = await registerPageCache();
        try {
          const b = await lazyBackend(url, ps === 1 ? 65536 : ps, total, versionOf(etag, null, total));
          b.mode += (cached ? "; pages cached across reloads" : "") + metaNote(u, total);
          return b;
        } catch (e) { why = `lazy loading failed: ${e.message || e}`; }
      }
      note = ` (${why})`;
      if (total > WHOLE_LIMIT) throw new TooLarge(u, total, why);
    }
    r = await fetch(url, { cache: "no-store" });
    if (!r.ok) throw new Error("HTTP " + r.status);
  } else why = "the server ignored the Range request";
  const bytes = whole ? new Uint8Array(await r.arrayBuffer()) : await readCapped(r, WHOLE_LIMIT, u, why);
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
    (be && be.changed && be.changed() ? '<p><button type="button" id="reopen">Open the new version</button></p>' : "") +
    '<h3>Open another database</h3><p><label>file <input type="file" class="dbfile" accept=".sqlite,.sqlite3,.db"></label> ' +
    '<span class="muted">read in the browser; nothing is uploaded</span></p>' +
    '<form class="dburl"><label>URL <input type="text" name="u" size="40" placeholder="project.sqlite or https://…"></label> <button type="submit">Open</button></form>' +
    (DB_URLS.length ? `<p class="muted">this page's default: <code>${esc(DB_URLS[0])}</code></p>` : "");
  const d = dialog({ title: "Database", body });
  wireFilePickers(d.el, d.close);
  const re = d.el.querySelector("#reopen");
  if (re) re.addEventListener("click", () => { d.close(); const u = source.label; openSource(u, () => openUrl(u)); });
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
  disposeRoute();
  routeTok++;   // the current view stops here: its late queries are superseded
  $("#main").innerHTML = `<div id="msg">Opening ${esc(label)}…</div>`;
  try {
    const b = await make();
    if (tok !== openTok) { if (b.close) b.close(); return false; }
    await useDb(b, label);
    return true;
  } catch (e) {
    if (tok !== openTok || e instanceof Superseded) return false;
    $("#main").innerHTML = `<div id="msg">${pickHelp(`<p class="err">could not open ${esc(label)}: ${esc(e.message || e)}</p>` + tooLargeOffer(e))}</div>`;
    wireFilePickers($("#main"));
    wireTooLarge($("#main"));
    return false;
  }
}
// The open database changed on the server: say so in the source button and dialog (for the
// database that is open now only; an old backend's late report is ignored).
function noteChanged(e) {
  if (!be || !be.changed || be.changed() !== e) return;
  source.problem = e.message;
  renderSource();
  window.explore.changed = { was: e.was, now: e.now || null, why: e.why || null };
}
// What a view shows instead when its database changed: the way to the new version.
function changedNotice(e) {
  return `<div class="note" role="alert"><p><b>The database changed.</b> ${esc(e.message)}</p>` +
    '<p><button type="button" id="reopen">Open the new version</button> <button type="button" id="pickother">Choose another database…</button></p></div>';
}
function wireChangedNotice(root) {
  const r = root.querySelector("#reopen"), o = root.querySelector("#pickother");
  if (r) r.addEventListener("click", () => { const u = source.label; openSource(u, () => openUrl(u)); });
  if (o) o.addEventListener("click", () => sourceDialog());
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
    catch (e) { tried.push(`<li><code>${esc(u)}</code>: ${esc(e.message || e)}${tooLargeOffer(e)}</li>`); continue; }
    if (tok !== openTok) { if (b.close) b.close(); return; }   // the reader chose a file meanwhile
    try { return await useDb(b, u); } catch (e) { if (e instanceof Superseded) return; throw e; }
  }
  if (tok !== openTok) return;
  $("#main").innerHTML = `<div id="msg">${pickHelp(`<p>No database could be opened from:</p><ul>${tried.join("")}</ul>`)}</div>`;
  wireFilePickers($("#main"));
  wireTooLarge($("#main"));
}
// A database too large to read whole by default: the reader may still ask for it.
function tooLargeOffer(e) {
  return e instanceof TooLarge ? ` <button type="button" class="loadwhole" data-url="${esc(e.url)}">Read it whole anyway${e.total ? ` (${esc(kB(e.total))})` : ""}</button>` : "";
}
function wireTooLarge(root) {
  for (const b of root.querySelectorAll("button.loadwhole")) b.addEventListener("click", () => {
    const u = b.dataset.url;
    openSource(u, () => openUrl(u, { whole: true }));
  });
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
  Object.assign(window.explore, { ready: true, mode: b.mode, source: label, opened: (window.explore.opened || 0) + 1, changed: null });
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

