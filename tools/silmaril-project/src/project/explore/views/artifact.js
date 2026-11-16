async function artifactPage(key, ctx) {
  const a = (await q("SELECT * FROM artifacts WHERE cid = ? OR sid = ? LIMIT 1", [key, key]))[0];
  if (!a) return `<p class="err">no artifact ${esc(key)}</p>`;
  let h = `<h2>Artifact <code>${esc(a.name || a.cid)}</code></h2>` + await dl(a, { cid: "", name: "" });
  // The bytes: from the project's repository at the page's commit (paths of the local package
  // only), read at most VIEWER_LIMIT bytes, checked against the registered SHA-256 when whole.
  const local = (await tq("projects", "SELECT name FROM projects WHERE origin = 'local' LIMIT 1"))[0];
  const paths = await first(DETAIL, "SELECT package, path FROM artifact_paths WHERE artifact = ?", [a.sid]);
  h += "<h2>Paths</h2>" + await tableOf(paths, ["package", "path", "bytes"], { render: { bytes: (r) => {
    const f = local && r.package === local.name ? repoFile(r.path) : null;
    return f ? `<button type="button" data-bytes="${esc(f.raw)}" data-name="${esc(r.path)}" data-sha256="${esc(a.sha256 || "")}"` +
      `${/\.wat$/i.test(r.path) ? ' data-lang="wat"' : ""}>view</button> <a href="${esc(f.blob)}" target="_blank" rel="noopener noreferrer">on GitHub</a>` : '<span class="muted">—</span>';
  } }, nowrap: ["bytes"] });
  h += await sections("artifact", { cid: a.cid, sid: a.sid, name: a.name, type: a.type, sha256: a.sha256, size: a.size }, ctx);
  h += "<h2>Facts</h2>" + await tableOf(await first(DETAIL, "SELECT at, property, value, checker, tier FROM facts WHERE subject = ? ORDER BY at, property", [a.sid]), null, { hints: { value: "" } });
  h += "<h2>Values read from it</h2>" + await tableOf(await first(DETAIL, "SELECT value, pos, format, obligation FROM value_sources WHERE cid = ?", [a.cid]));
  h += "<h2>Problems over it</h2>" + await tableOf(await first(DETAIL, "SELECT problem, pos, 'input' AS via FROM problem_inputs WHERE cid = ? " +
    "UNION ALL SELECT problem, pos, 'instance_arg' FROM instance_args WHERE cid = ?", [a.cid, a.cid]));
  return h;
}

// ---------- Wasm: components, modules, functions ----------
// Static files written by `wasm-pages` (tools/wasm-pages) next to the page: wasm/index.json,
// wasm/c/<slug>.json (components), wasm/m/<slug>.json (modules, with their functions), and the
// downloads wasm/blob/<slug>.wasm and wasm/wat/<slug>.wat. Nothing here is read from the
// database. Every fact says where it comes from: the Lean decoders, printers and validator ran
// at build time ("Lean, runtime"); graphs drawn here are syntactic; dominators of the block CFGs
// are computed in the browser, except where a Lean kernel-checked table exists for the same graph.

registerView({ id: "artifact", title: "Artifact", tab: "artifacts", render: artifactPage });
