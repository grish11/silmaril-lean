// Public, hash-addressed corpus evidence. No fixture exporter/proof-status adapter.
const $ = id => document.getElementById(id);
function el(tag, text, cls) {
  const e = document.createElement(tag);
  if (text !== undefined) e.textContent = String(text);
  if (cls) e.className = cls;
  return e;
}
function link(text, href) { const a = el('a', text); a.href = href; return a; }
async function json(path) {
  const r = await fetch(path);
  if (!r.ok) throw new Error(`${path}: ${r.status}`);
  return r.json();
}
async function text(resource) {
  const response = await fetch(resource.static_path);
  if (!response.ok) throw new Error(`missing corpus evidence: ${response.status}`);
  const bytes = await response.arrayBuffer();
  const digest = [...new Uint8Array(await crypto.subtle.digest('SHA-256', bytes))].map(b => b.toString(16).padStart(2, '0')).join('');
  if (digest !== resource.sha256 || bytes.byteLength !== resource.size) throw new Error('corpus evidence identity mismatch');
  return new TextDecoder('utf-8', {fatal:true}).decode(bytes);
}
function lines(box, value) {
  box.replaceChildren();
  for (const [i, line] of value.split('\n').entries()) {
    const row = el('div', undefined, 'line');
    row.append(el('span', i + 1, 'ln'), el('span', line || ' ', 'tx'));
    box.append(row);
  }
}
export async function initCorpus() {
  const wanted = new URLSearchParams(location.search).get('corpus');
  let listing;
  const response = await fetch('api/corpus/index.json');
  if (!response.ok) {
    if (wanted) throw new Error('this viewer has no corpus statement export');
    return false; // Standalone fixture server predates static Pages corpus exports.
  }
  listing = await response.json();
  const picker = $('corpus-statement');
  for (const p of listing) picker.append(new Option(`${p.function_symbol} · UNPROVED`, p.declaration));
  picker.onchange = () => { if (picker.value) location.search = '?corpus=' + encodeURIComponent(picker.value); };
  if (!wanted) return false;
  const entry = listing.find(p => p.declaration === wanted);
  if (!entry) throw new Error('unregistered corpus statement');
  picker.value = wanted;
  const p = await json(entry.static_path);
  if (p.status !== 'UNPROVED' || p.declaration !== wanted || p.proof_evidence !== null || p.exporter_run !== null) throw new Error('unexpected corpus statement identity/status');
  document.querySelector('.pickers').hidden = true;
  document.querySelector('h1 .sub').textContent = 'actual source / Core / ELF · stated, unproved';
  document.querySelector('header .note').textContent = 'Read-only registered corpus statements. All corpus refinements are UNPROVED. Source and identity checks are separate from semantic correctness; no compiler service runs here.';
  const git = path => `https://github.com/hiloopai/silmaril-lean/blob/${p.revision}/${path.split('/').map(encodeURIComponent).join('/')}`;
  $('source-title').textContent = `Actual source closure · ${p.function_symbol}`;
  $('target-title').textContent = 'Real ELF function bytes · tool-checked excerpt';
  lines($('source'), await text(p.source));
  const excerpt = (symbol, f) => `${symbol} @ 0x${f.address.toString(16)} · ${f.size} bytes · file offset ${f.file_offset}\n${f.bytes_hex}\nFunction bytes sha256 ${f.code_sha256}\n${f.identity_check}`;
  const target = p.artifacts.map(a => `${a.path}\nELF sha256 ${a.sha256}\n${excerpt(p.function_symbol, a)}${(a.callees || []).map(c => '\n\nActual callee excerpt (not a substituted contract)\n' + excerpt(c.function_symbol, c)).join('')}`).join('\n\n');
  const dataEvidence = p.artifacts.flatMap(a => (a.data_bindings || []).map(d =>
    `Actual ELF data object (separate from function CodeAt)\n${d.symbol} @ 0x${d.address.toString(16)} · ${d.size} bytes · file offset ${d.file_offset}\n${d.bytes_hex}\nData sha256 ${d.sha256}\nActual raw RELA @ file offset ${d.relocation.file_offset}\n${d.relocation.bytes_hex}\n${d.relocation.type} · symbol index ${d.relocation.symbol_index} · addend ${d.relocation.addend} · GOT slot 0x${d.relocation.slot.toString(16)} · raw ELF file offset ${d.relocation.slot_file_offset}\nRaw GOT slot bytes ${d.relocation.slot_bytes_hex} (before loader resolution)\n${d.limit}`));
  lines($('target'), [target, ...dataEvidence].join('\n\n'));
  const selection = $('selection');
  selection.replaceChildren(el('h2', 'Registered corpus problem'), el('span', 'UNPROVED', 'badge st-open'), el('code', p.declaration, 'stmt'), el('p', p.mapping));
  const navigation = el('p');
  navigation.append(link('Corpus catalog', '../#/corpus'), document.createTextNode(' · '), link('Compiler integration', '../#/compiler'));
  selection.append(navigation, link('Exact Lean statement', git(p.root.replaceAll('.', '/') + '.lean')));
  const panes = el('p');
  panes.append(link('Source', '#src'), document.createTextNode(' · '), link('Core and context', '#corpus-core'), document.createTextNode(' · '), link('ELF bytes', '#tgt'));
  selection.append(panes);
  for (const a of p.artifacts) {
    const row = el('p');
    row.append(link('Corpus artifact', '../#/corpus-artifact/' + encodeURIComponent(a.id)), document.createTextNode(' · '),
      link('Corpus function', '../#/corpus-functions/' + encodeURIComponent(a.id) + '?symbol=' + encodeURIComponent(p.function_symbol)), document.createTextNode(' · '), link('ELF in Git', git(a.path)));
    selection.append(row);
    for (const c of a.callees || []) {
      const callee = el('p');
      callee.append(link(`Actual callee ${c.function_symbol}`, '../#/corpus-functions/' + encodeURIComponent(a.id) + '?symbol=' + encodeURIComponent(c.function_symbol)), document.createTextNode(` · 0x${c.address.toString(16)} · ${c.size} bytes · same pinned ELF`));
      selection.append(callee);
    }
  }
  $('questions').replaceChildren(el('h2', 'Context obligations'), el('p', 'Joint entry existence, source safety, ABI return and memory/callee effects remain obligations, not proved facts. Read the exact defining context below.'));
  const provenance = $('provenance');
  provenance.replaceChildren(el('h2', 'Source / Core identity'));
  for (const [role, resource] of [['Source', p.source], ['Core', p.core], ...(p.runtime ? [['Runtime', p.runtime]] : [])]) {
    const r = el('p', `${role} sha256 ${resource.sha256} · ${resource.size} bytes`);
    r.dataset.evidenceRole = role;
    provenance.append(r, link(`${role} public input`, git(resource.path || resource.module)));
  }
  const span = el('pre', JSON.stringify(p.source.projection, null, 2));
  span.id = 'corpus-source-spans';
  provenance.append(el('h3', 'Exact source spans'), span, link('Source TU in Git', git(p.source.projection.tu)), el('p', `Public revision ${p.revision}`), link('Registry and pins', git(p.registry.path)), el('p', `Viewer manifest sha256 ${p.manifest.sha256}`), link('Viewer manifest', git(p.manifest.path)), link('Measured check receipt (not a semantic proof)', git(p.run_receipt)));
  $('assumptions').replaceChildren(el('h2', 'Assumptions and provenance limits'));
  const limits = el('ul');
  for (const value of p.limits) limits.append(el('li', value));
  $('assumptions').append(limits);
  const evidence = $('corpus-evidence');
  evidence.hidden = false;
  evidence.replaceChildren(el('h2', 'Actual Core and ABI / memory / callee / UB context'));
  const core = el('pre', await text(p.core)); core.id = 'corpus-core';
  evidence.append(el('p', 'Recorded Core input and its exact defining modules. Whole closure is displayed; no instruction-level correspondence is invented.'), core);
  for (const resource of p.context_modules) {
    const details = el('details');
    details.append(el('summary', `${resource.path} · sha256 ${resource.sha256}`), link('Pinned module', git(resource.path)), el('pre', await text(resource)));
    details.dataset.contextModule = resource.path;
    evidence.append(details);
  }
  $('status').textContent = `${listing.length} registered corpus statements · UNPROVED · no interactive compilation · ${p.function_symbol}`;
  document.body.dataset.corpusDeclaration = p.declaration;
  return true;
}
