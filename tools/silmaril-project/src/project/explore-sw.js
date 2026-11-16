// Written by `sil project explore` next to the page (tools/silmaril-project/src/project/explore-sw.js).
// A service worker that keeps the database pages the explorer reads lazily, across reloads.
// It only touches GET requests that carry a Range header and the page's version-tagged query
// (`?v=<version>&part=<n>`); everything else goes to the network untouched. Entries are keyed
// by path, version and range, so pages of two versions are never mixed; when a new version of a
// file is read, the entries of its other versions are deleted. A response is cached only when it
// is a 206 of the version its URL names (strong ETag, else Last-Modified, and the length, as the
// page's `versionOf`), and a hit is served with the validators it came with, so the page's
// per-read version check applies to cached pages as to fresh ones.
"use strict";
const CACHE = "silmaril-explore-db-pages-v2";
self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", (e) => e.waitUntil((async () => {
  // v1 entries kept no validators: drop them (and any other old cache of this worker)
  for (const k of await caches.keys()) if (k.startsWith("silmaril-explore-db-pages-") && k !== CACHE) await caches.delete(k);
  await self.clients.claim();
})()));
function versionOf(etag, lastModified, total) {
  return ((etag && !etag.startsWith("W/") ? etag : lastModified) || "").replace(/[^A-Za-z0-9._-]/g, "") + "-" + total;
}
self.addEventListener("fetch", (e) => {
  const req = e.request;
  if (req.method !== "GET") return;
  const u = new URL(req.url);
  const v = u.searchParams.get("v"), part = u.searchParams.get("part");
  const range = req.headers.get("range");
  if (!v || part === null || !range) return;
  const key = `${u.origin}${u.pathname}?v=${encodeURIComponent(v)}&part=${encodeURIComponent(part)}&range=${encodeURIComponent(range)}`;
  e.respondWith((async () => {
    const cache = await caches.open(CACHE);
    const hit = await cache.match(key);
    if (hit) {
      const h = new Headers(hit.headers);
      h.set("content-range", h.get("x-content-range") || "");
      h.set("x-silmaril-cache", "hit");
      return new Response(await hit.arrayBuffer(), { status: 206, headers: h });
    }
    const r = await fetch(req);
    const cr = /^bytes (\d+)-(\d+)\/(\d+)$/.exec(r.headers.get("content-range") || "");
    const want = /^bytes=(\d+)-(\d+)$/.exec(range);
    const sameVersion = cr && versionOf(r.headers.get("etag"), r.headers.get("last-modified"), cr[3]) === v;
    const exact = cr && want && cr[1] === want[1] && cr[2] === want[2];
    if (r.status === 206 && sameVersion && exact && !(r.headers.get("content-encoding") || "").match(/gzip|br|deflate/)) {
      const body = await r.clone().arrayBuffer();
      const h = new Headers({ "x-content-range": r.headers.get("content-range") || "",
        "content-type": r.headers.get("content-type") || "application/octet-stream" });
      for (const k of ["etag", "last-modified"]) if (r.headers.get(k)) h.set(k, r.headers.get(k));
      // Cache.put refuses 206 responses: store the bytes as a 200 and rebuild the 206 on a hit.
      await cache.put(key, new Response(body, { status: 200, headers: h }));
      for (const k of await cache.keys()) {
        const ku = new URL(k.url);
        if (ku.origin + ku.pathname === u.origin + u.pathname && ku.searchParams.get("v") !== v) await cache.delete(k);
      }
    }
    return r;
  })());
});
