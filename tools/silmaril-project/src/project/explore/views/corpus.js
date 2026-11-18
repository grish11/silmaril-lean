// A dedicated corpus view over additive metadata tables. No ELF bytes are embedded.
async function corpusPage(arg, ctx) {
  if (!tables.has("corpus_artifacts")) return '<h2>Corpus</h2><p>No corpus inventory is available in this database.</p>';
  const counts = (await ctx.q("SELECT (SELECT count(*) FROM corpus_artifacts) artifacts,(SELECT count(DISTINCT project) FROM corpus_artifacts) projects,(SELECT count(DISTINCT sha256) FROM corpus_artifacts) hashes"))[0];
  const statementCounts = Object.fromEntries((await ctx.q("SELECT key,value FROM corpus_meta WHERE key LIKE '%_statements'")).map(r=>[r.key,Number(r.value)]));
  const tvCount=statementCounts.contextual_c_to_elf_statements||0, eqCount=statementCounts.functional_equivalence_statements||0;
  const columns={project:'project',version:'version',configuration:"json_extract(metadata,'$.build.configuration')",target:'target',optimization:'optimization',stripping:'stripping'};
  const choices = {};
  for (const [column,expression] of Object.entries(columns))
    choices[column] = await ctx.q(`SELECT DISTINCT ${expression} value FROM corpus_artifacts ORDER BY value`);
  const select = (column) => `<label>${esc(column)} <select data-corpus-filter="${column}" aria-label="${column}"><option value="">All</option>${choices[column].map(r => `<option>${esc(r.value)}</option>`).join("")}</select></label>`;
  return { html: `<section><h2>Software under test</h2><p class="muted">Browse projects, releases, build settings and exact artifacts.</p>
    ${tables.has("projects") ? '<p><a href="#/compiler">Compiler explorer integration and source ↔ target viewer</a></p>' : ""}
    <div class="corpus-metrics"><div><h3>${counts.projects} projects</h3><p>${counts.artifacts} delivered artifact rows · ${counts.hashes} unique contents</p></div>
    <div><h3>${tvCount} contextual C → ELF statements</h3><p>${eqCount} function-equivalence statements · stated, unproved. Source metadata and structural decompositions remain separate from semantic validation.</p></div></div>
    <p>Only completed, hash-checked artifacts appear. Instruction census results are static tool evidence; imports do not demonstrate runtime use.</p>
    <div class="corpus-filters" id="corpus-filters">${Object.keys(choices).map(select).join(" ")}</div>
    <p id="corpus-count" aria-live="polite"></p><div id="corpus-results"></div></section>`,
    init: async () => {
      let request = 0;
      const refresh = async () => {
        const token = ++request;
        const clauses = [], params = [];
        for (const element of document.querySelectorAll("[data-corpus-filter]")) if (element.value) {
          clauses.push(columns[element.dataset.corpusFilter] + " = ?"); params.push(element.value);
        }
        const where = clauses.length ? " WHERE " + clauses.join(" AND ") : "";
        const rows = await ctx.q("SELECT id,project,version,target,optimization,stripping,name,sha256,json_extract(metadata,'$.build.configuration') configuration,json_extract(metadata,'$.lean_status') lean_status,json_extract(metadata,'$.functional_equivalence_statements') equivalence_statements,json_extract(metadata,'$.contextual_c_to_elf_statements') tv_statements FROM corpus_artifacts" + where + " ORDER BY project,version,target,optimization,stripping,name LIMIT 1000", params);
        if (!ctx.alive() || token !== request) return;
        document.querySelector("#corpus-count").textContent = `${rows.length} matching artifacts${rows.length === 1000 ? ' (first 1,000)' : ''}`;
        document.querySelector("#corpus-results").innerHTML = `<table><thead><tr><th>Project / release</th><th>Build</th><th>Artifact</th><th>Coverage</th></tr></thead><tbody>${rows.map(r => {
          return `<tr><td><strong>${esc(r.project)}</strong><br>${esc(r.version)}</td><td>${esc(r.target)}<br>${esc(r.configuration)}<br><code>-${esc(r.optimization)}</code> · ${esc(r.stripping)}</td><td><a href="#/corpus-artifact/${encodeURIComponent(r.id)}">${esc(r.name)}</a><br><small><code>${esc(r.sha256.slice(0, 16))}…</code></small></td><td>${esc(r.lean_status)}<br><span class="muted">TV: ${Number(r.tv_statements)||0} stated · equivalence: ${Number(r.equivalence_statements)||0} stated</span></td></tr>`;
        }).join("")}</tbody></table>`;
      };
      for (const element of document.querySelectorAll("[data-corpus-filter]")) element.addEventListener("change", () => refresh().catch(e => { if (ctx.alive()) document.querySelector("#corpus-count").textContent = e.message; }));
      await refresh();
    } };
}

async function corpusArtifact(id, ctx) {
  const [row] = await ctx.tq("corpus_artifacts", "SELECT * FROM corpus_artifacts WHERE id=?", [id]);
  if (!row) return '<p>Artifact not found.</p>';
  const m = JSON.parse(row.metadata), census = row.census && JSON.parse(row.census);
  const functions = await ctx.q("SELECT * FROM corpus_functions WHERE artifact=? ORDER BY symbol LIMIT 500", [id]);
  const count = (await ctx.q("SELECT count(*) n FROM corpus_functions WHERE artifact=?", [id]))[0].n;
  const revision = (await ctx.q("SELECT value FROM corpus_meta WHERE key='revision'"))[0].value;
  const file = path => `https://github.com/hiloopai/silmaril-lean/blob/${encodeURIComponent(revision)}/${path.split('/').map(encodeURIComponent).join('/')}`;
  const pretty = value => `<pre>${esc(JSON.stringify(value, null, 2))}</pre>`;
  return `<p><a href="#/corpus">← Corpus</a></p><h2>${esc(row.project)} ${esc(row.version)} · ${esc(row.name)}</h2>
    <p>${esc(row.target)} · -${esc(row.optimization)} · ${esc(row.stripping)} · ${esc(m.license)}</p>
    <p><a href="${file(row.path)}">Canonical ELF in Git</a> · <a href="${file(m.receipt)}">Build receipt</a></p>
    <dl><dt>SHA-256</dt><dd><code>${esc(row.sha256)}</code></dd><dt>Source identity</dt><dd><code>${esc(row.source_id)}</code></dd><dt>Build identity</dt><dd><code>${esc(row.build_id)}</code></dd></dl>
    ${m.formal_statements?.length?`<h3>Concrete function problems</h3>${m.formal_statements.map(s=>`<p><a href="${file(s.root.replaceAll('.','/')+'.lean')}">${esc(s.declaration)}</a> · ${esc(s.kind)} · ${esc(s.status)}</p>`).join('')}`:''}
    <h3>Verification coverage</h3><p>${esc(m.lean_status)}. Contextual C → ELF statements: ${Number(m.contextual_c_to_elf_statements)||0}. Functional equivalence statements: ${Number(m.functional_equivalence_statements)||0} (stated, unproved).</p>
    <h3>Build configuration</h3>${pretty(m.build)}
    <p><a href="#/corpus-timings/${encodeURIComponent(row.build_id)}">Measured build stages</a> · <a href="#/corpus-timings">All measured stages</a></p>
    <h3>Dependencies and instruction evidence</h3>${census ? `<p>Static tool evidence; runtime use and semantic support are not established.</p>${pretty({tools:census.tools, sections:census.executable_sections.map(s=>({name:s.name,size:s.size,decoded_bytes:s.decoded_bytes,undecoded_bytes:s.undecoded_bytes,unreported_bytes:s.unreported_bytes})), dynamic:census.dynamic, relocations:census.relocations, abi:census.abi_evidence, extensions:census.extension_evidence})}` : '<p>Not measured for this variant. No canonical-build census is silently reused.</p>'}
    <h3>Included source inputs</h3>${pretty(JSON.parse(row.sources))}
    <h3>Source mapping evidence</h3>${pretty(m.source_mapping_evidence)}
    <h3>Function mappings</h3><p><a href="#/corpus-functions/${encodeURIComponent(id)}">Search all ${count} symbol rows</a> (aliases included). Previewing at most 500. Paired stripped addresses and DWARF mappings are tool evidence, not source semantics. The x86 OpenSSL libcrypto debug-twin source mapping is provisional.</p>
    <table><thead><tr><th>Symbol</th><th>Address</th><th>Size</th><th>Mapping</th></tr></thead><tbody>${functions.map(f => `<tr><td>${esc(f.symbol)}</td><td>0x${Number(f.address).toString(16)}</td><td>${esc(f.size)}</td><td><details><summary>Evidence</summary>${pretty(JSON.parse(f.mapping))}</details></td></tr>`).join("")}</tbody></table>
    <h3>Runtime tests</h3>${pretty(m.runtime_tests)}`;
}
async function corpusTimings(build, ctx) {
  let runs=await ctx.tq('corpus_timing_summary','SELECT * FROM corpus_timing_summary'+(build?' WHERE build_id=?':'')+' ORDER BY stage,run_id',build?[build]:[]);
  // Older catalog files predate the compact index. Preserve their readability.
  if(!runs.length) runs=(await ctx.tq('corpus_timings',`SELECT run_id,build_id,stage,json_extract(metadata,'$.wall_seconds') wall_seconds,json_extract(metadata,'$.peak_rss_kib') peak_rss_kib,json_extract(metadata,'$.exit_code') exit_code FROM corpus_timings`+(build?' WHERE build_id=?':'')+' ORDER BY stage,run_id',build?[build]:[]));
  return {html:`<p><a href="#/corpus">← Corpus</a></p><h2>Measured pipeline stages</h2><p>${runs.length} actual run receipts. Cache state, concurrency and runner identity are recorded per run. Times cover each command's measured scope; overlapping stages must not be summed as end-to-end cost.</p>
    <p><label>Stage <select id="timing-stage" aria-label="Stage"><option value="">All stages</option>${[...new Set(runs.map(r=>r.stage))].map(stage=>`<option>${esc(stage)}</option>`).join('')}</select></label></p><p>Full receipts load when opened. <button id="timing-prev">Previous</button> <span id="timing-page"></span> <button id="timing-next">Next</button></p>
    <table><thead><tr><th>Stage</th><th>Wall seconds</th><th>Peak RSS KiB</th><th>Exit</th><th>Receipt</th></tr></thead><tbody id="timing-rows"></tbody></table>`,
    init:async()=>{
      let start=0; const size=100; let filtered=runs;
      const render=()=>{
        document.querySelector('#timing-rows').innerHTML=filtered.slice(start,start+size).map(r=>`<tr><td>${esc(r.stage)}</td><td>${Number(r.wall_seconds).toFixed(3)}</td><td>${esc(r.peak_rss_kib)}</td><td>${esc(r.exit_code)}</td><td><details data-timing-run="${esc(r.run_id)}"><summary>${esc(r.run_id.slice(0,8))}</summary><pre>Open to load receipt</pre></details></td></tr>`).join('');
        document.querySelector('#timing-page').textContent=`${filtered.length?start+1:0}–${Math.min(start+size,filtered.length)} of ${filtered.length}`;
        document.querySelector('#timing-prev').disabled=start===0;
        document.querySelector('#timing-next').disabled=start+size>=filtered.length;
      };
      document.querySelector('#timing-stage').onchange=event=>{filtered=runs.filter(r=>!event.target.value||r.stage===event.target.value);start=0;render();};
      document.querySelector('#timing-prev').onclick=()=>{start=Math.max(0,start-size);render();};
      document.querySelector('#timing-next').onclick=()=>{start+=size;render();};
      document.querySelector('#timing-rows').addEventListener('toggle',async event=>{
        const detail=event.target;
        if(!detail.matches('details[data-timing-run]')||!detail.open||detail.dataset.loaded)return;
        detail.dataset.loaded='true'; const pre=detail.querySelector('pre');pre.textContent='Loading receipt…';
        try{
          const [row]=await ctx.q('SELECT metadata FROM corpus_timings WHERE run_id=?',[detail.dataset.timingRun]);
          if(ctx.alive()&&detail.isConnected)pre.textContent=row?JSON.stringify(JSON.parse(row.metadata),null,2):'Receipt not found';
        }catch(error){if(ctx.alive()&&detail.isConnected)pre.textContent=error.message;}
      },true);
      render();
    }};
}

async function corpusFunctions(id, ctx) {
  const [artifact] = await ctx.tq("corpus_artifacts", "SELECT name,metadata FROM corpus_artifacts WHERE id=?", [id]);
  if (!artifact) return '<p>Artifact not found.</p>';
  return {html:`<p><a href="#/corpus-artifact/${encodeURIComponent(id)}">← Artifact</a></p><h2>${esc(artifact.name)} · Function mappings</h2>
    <p>Symbol rows include aliases. Metadata is not source semantics. This artifact has ${Number(JSON.parse(artifact.metadata).contextual_c_to_elf_statements)||0} contextual C → ELF statements (stated, unproved); see the artifact verification links for their exact scope.</p>
    <label>Symbol contains <input id="corpus-function-search" type="search"></label><p id="corpus-function-count" aria-live="polite"></p><div id="corpus-functions"></div>`,
    init:async()=>{
      let request=0;
      const refresh=async()=>{
        const token=++request, search=document.querySelector('#corpus-function-search').value;
        const params=[id,'%'+search+'%'];
        const count=(await ctx.q('SELECT count(*) n FROM corpus_functions WHERE artifact=? AND symbol LIKE ?',params))[0].n;
        const rows=await ctx.q('SELECT * FROM corpus_functions WHERE artifact=? AND symbol LIKE ? ORDER BY symbol LIMIT 200',params);
        if(!ctx.alive()||token!==request)return;
        document.querySelector('#corpus-function-count').textContent=`${count} matching symbol rows · showing ${rows.length}`;
        document.querySelector('#corpus-functions').innerHTML=rows.map(f=>`<details><summary><strong>${esc(f.symbol)}</strong> · 0x${Number(f.address).toString(16)} · ${esc(f.size)} bytes</summary><pre>${esc(JSON.stringify(JSON.parse(f.mapping),null,2))}</pre></details>`).join('');
      };
      document.querySelector('#corpus-function-search').addEventListener('input',()=>refresh().catch(e=>{if(ctx.alive())document.querySelector('#corpus-function-count').textContent=e.message;}));
      await refresh();
    }};
}
registerView({id:"corpus", title:"Corpus", nav:17, render:corpusPage});
registerView({id:"corpus-artifact", title:"Corpus artifact", tab:"corpus", render:corpusArtifact});
registerView({id:"corpus-functions", title:"Corpus functions", tab:"corpus", render:corpusFunctions});
registerView({id:"corpus-timings", title:"Corpus timings", tab:"corpus", render:corpusTimings});
