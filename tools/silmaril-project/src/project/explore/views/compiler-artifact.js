let compilerCatalog;

function compilerArtifacts() {
  compilerCatalog ??= fetch("compiler-artifacts/index.json").then(async (response) => {
    if (!response.ok) throw new Error(`compiler artifact catalog: HTTP ${response.status}`);
    const doc = await response.json();
    if (doc.schema !== "silmaril.compiler-artifacts/1") throw new Error("unsupported compiler artifact catalog");
    return doc.artifacts;
  });
  return compilerCatalog;
}

async function compilerArtifactIndex(tab) {
  try {
    const artifacts = await compilerArtifacts();
    const rows = Object.entries(artifacts).filter(([, entry]) => entry.tab === tab);
    return `<h2>${tab === "c" ? "C source artifacts" : "Compiler ELF artifacts"}</h2>` +
      "<p>Exact compiler-explorer bytes, identified by SHA-256. These pages do not attach proof status.</p>" +
      `<ul>${rows.map(([sha, entry]) => `<li><a href="#/${tab}-artifact/${sha}">${esc(entry.paths[0])}</a>` +
        ` · ${entry.size} bytes · <code>${sha.slice(0, 12)}…</code></li>`).join("")}</ul>`;
  } catch (error) {
    return `<p class="muted">${esc(error.message)}. Run <code>make pages</code> to publish compiler artifacts.</p>`;
  }
}

function compilerElfSections(bytes) {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  if (bytes.length < 64 || view.getUint32(0) !== 0x7f454c46 || bytes[4] !== 2 || bytes[5] !== 1) {
    return "<p>Section inspection covers only little-endian ELF64.</p>";
  }
  const size = view.getUint16(58, true), count = view.getUint16(60, true), names = view.getUint16(62, true);
  const tableOffset = view.getBigUint64(40, true);
  let html = `<p>ELF64 little-endian · type ${view.getUint16(16, true)} · machine ${view.getUint16(18, true)}. ` +
    "Section metadata is read by this browser, not verified in Lean.</p>";
  if (!count || size !== 64 || names >= count || tableOffset + BigInt(size * count) > BigInt(bytes.length)) {
    return html + "<p>No supported section table.</p>";
  }
  const table = Number(tableOffset), strings = table + names * size;
  const start = view.getBigUint64(strings + 24, true), length = view.getBigUint64(strings + 32, true);
  const nameBytes = start + length <= BigInt(bytes.length) ? bytes.subarray(Number(start), Number(start + length)) : new Uint8Array();
  const decoder = new TextDecoder();
  const rows = [];
  for (let index = 0; index < count; index++) {
    const pos = table + index * size;
    const offset = view.getUint32(pos, true), end = nameBytes.indexOf(0, offset);
    const name = end < 0 ? "" : decoder.decode(nameBytes.subarray(offset, end));
    const fileOffset = view.getBigUint64(pos + 24, true), sectionSize = view.getBigUint64(pos + 32, true);
    const kind = view.getUint32(pos + 4, true);
    rows.push(`<tr><td>${index}</td><td><code>${esc(name)}</code></td><td>${kind}</td>` +
      `<td>${kind === 8 ? "not in file" : `0x${fileOffset.toString(16)}`}</td><td>${sectionSize}</td></tr>`);
  }
  return html + "<h3>Sections</h3><div class=tablebox><table><thead><tr><th>#</th><th>Name</th><th>Type</th>" +
    `<th>File offset</th><th>Size</th></tr></thead><tbody>${rows.join("")}</tbody></table></div>`;
}

function compilerElfBlock(bytes, block) {
  const [lo, hi] = block.file_range;
  if (!Number.isSafeInteger(lo) || !Number.isSafeInteger(hi) || lo < 0 || lo >= hi || hi > bytes.length) {
    throw new Error("block range is outside the verified ELF bytes");
  }
  const hex = [...bytes.subarray(lo, hi)].map((part) => part.toString(16).padStart(2, "0")).join(" ");
  return `<h3>Decoded block candidate · ${esc(block.symbol)}</h3>` +
    `<p>Section ${esc(block.section)} · file bytes [${lo}, ${hi}) · model entry 0x${esc(block.model_base.toString(16))}</p>` +
    `<pre>${esc(hex)}</pre><p>These are the exact selected bytes, not a CFG or a loader certificate. ` +
    `<a href="compiler/?problem=${encodeURIComponent(block.problem)}">Inspect its source-fragment attribution</a>.</p>`;
}

async function compilerArtifactPage(tab, key) {
  try {
    const [sha, blockId, ...rest] = key.split("/");
    if (!/^[a-f0-9]{64}$/.test(sha)) throw new Error("expected a full SHA-256");
    const entry = (await compilerArtifacts())[sha];
    if (!entry || entry.tab !== tab) throw new Error("no such published artifact in this tab");
    const block = blockId && entry.blocks?.[blockId];
    if (rest.length || (blockId && (tab !== "elf" || !/^[a-f0-9]{64}$/.test(blockId) || !block))) {
      throw new Error("no such published block for this artifact");
    }
    const url = `compiler-artifacts/bytes/${sha}`;
    const response = await fetch(url);
    if (!response.ok) throw new Error(`artifact bytes: HTTP ${response.status}`);
    const bytes = new Uint8Array(await response.arrayBuffer());
    const digest = new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
    if (bytes.length !== entry.size || [...digest].map((part) => part.toString(16).padStart(2, "0")).join("") !== sha) {
      throw new Error("published bytes do not match the artifact address");
    }
    const rendered = viewer(bytes, { total: bytes.length });
    return { html: `<h2>${tab.toUpperCase()} artifact · ${esc(entry.paths[0])}</h2>` +
      `<p>SHA-256 verified against these bytes: <code>${sha}</code> · <a href="${url}" download>download exact bytes</a></p>` +
      (block ? compilerElfBlock(bytes, block) : "") +
      (tab === "elf" && !block ? Object.entries(entry.blocks || {}).map(([id, b]) =>
        `<p><a href="#/elf-artifact/${sha}/${esc(id)}">Inspect ${esc(b.symbol)} block candidate</a></p>`).join("") : "") +
      (tab === "elf" ? compilerElfSections(bytes) : "") + rendered.html, init: () => rendered.init() };
  } catch (error) {
    return `<p class="err">${esc(error.message)}</p>`;
  }
}

registerView({ id: "c-artifacts", title: "C", nav: 84, render: () => compilerArtifactIndex("c") });
registerView({ id: "c-artifact", title: "C artifact", tab: "c-artifacts", render: (sha) => compilerArtifactPage("c", sha) });
registerView({ id: "elf-artifact", title: "Compiler ELF artifact", tab: "elf", render: (sha) => compilerArtifactPage("elf", sha) });
