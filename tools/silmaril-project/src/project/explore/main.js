// ---------- start ----------
// Every view has registered itself by now (explore.rs bundles main.js last).
boot().catch((e) => { $("#main").innerHTML = `<p class="err">${esc(e.stack || e)}</p>`; });
