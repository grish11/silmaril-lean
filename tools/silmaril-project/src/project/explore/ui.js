// ---------- shared components ----------
// Small components every view can use (and `Explorer.ui` exports): links, status badges, a
// modal dialog and a bounded byte viewer. They return HTML strings or wire up elements; every
// piece of text they show is escaped, since names, titles and file contents are untrusted.
function href(kind, key) { return "#/" + kind + "/" + encodeURIComponent(key); }
function link(kind, key, text) { return `<a href="${href(kind, key)}">${esc(text == null ? key : text)}</a>`; }
// A plain tag (`badge("holds")`): the verdict colours of the graph legend.
function badge(v, text) { return v ? `<span class="badge ${esc(v)}">${esc(text || v)}</span>` : ""; }

// Status badges. The semantics (displayed codes by arity, expectation outcomes by entailment,
// attention lists) live in status.js (`StatusSemantics`); this is their presentation.
// A badge shows one displayed code: THM/CTH for a problem without parameters, TAU/UNS/SAT/CSA/NOC
// for one with parameters, OPN/UNK when nothing is known. Nothing is shown when the status is what
// was expected or nothing was expected; otherwise a second chip names the expectation and how the
// status differs from it ("expected UNS": less information, "≠ TAU": contrary, "+": more than
// expected). The title (and the screen-reader label) explains the code, the stored codes, the
// arity, the expectation and the markings. Deprecated problems are struck through. `data-code` is
// the stored summary, `data-display` the displayed code, `data-outcome` the outcome.
const SZS_SOURCE = "https://szs.tptp.org/success";
// The displayed code of a stored code without context (a closed reading needs the arity: see
// `statusInfo`). Kept for callers that have only a code.
function statusCode(code) { return code === "contingent" ? "NOC" : code; }
// A one-line explanation of a displayed or stored code.
function statusText(code) {
  const shown = statusCode(code);
  const d = StatusSemantics.DISPLAY_CODES[shown];
  return `${shown}${d ? " (" + d.name + ")" : ""}: ${d ? d.text : "status code"}` + (shown !== code ? `; stored as "${code}"` : "");
}
// name -> { summary, verdict, expect, arity, established, deprecated, finding, expectedOpen }
// (filled by `resolve` and the graph)
let statusOf = new Map();
// Legacy outcome names (`expectationSummary`, the language and system views): met, mismatch,
// pending, unset, error.
const LEGACY_OUTCOME = { match: "match", stronger: "match", contrary: "mismatch", weaker: "pending", none: "none", error: "error" };
function statusInfo(s) {
  if (!s || !s.summary) return null;
  const st = StatusSemantics.problemStatus(s);
  const cls = st.outcome === "contrary" || st.outcome === "error" ? "bad" : st.outcome === "weaker" ? "less" : st.outcome === "stronger" ? "more" : "";
  // an expected OPN that is still open counts as no expectation in aggregates (nothing to meet)
  const legacy = st.outcome === "match" && (st.expect === "OPN" || st.expect === "UNK") ? "none" : LEGACY_OUTCOME[st.outcome];
  return Object.assign(st, { legacy, cls, dep: !!st.deprecated, title: StatusSemantics.statusExplanation(st) });
}
// An aggregate over several problems' expectations (e.g. a language's examples): how many are met
// (as expected or more), mismatched (contrary), pending (less than expected), unset or errors.
// `allMet` only when every one has an expectation and meets it.
function expectationSummary(list) {
  const out = { total: 0, met: 0, mismatch: 0, pending: 0, unset: 0, error: 0 };
  for (const s of list) {
    const i = statusInfo(s);
    out.total++;
    if (!i) { out.unset++; continue; }
    out[{ match: "met", mismatch: "mismatch", pending: "pending", none: "unset", error: "error" }[i.legacy]]++;
  }
  out.allMet = out.total > 0 && out.met === out.total;
  return out;
}
// The chip after a code that says how it differs from the expectation ("" when it does not).
function expectationChip(i) {
  if (!i.expect && i.outcome !== "error") return "";
  if (i.outcome === "error") return '<span class="st-x st-x-bad">error</span>';
  if (i.outcome === "contrary") return `<span class="st-x st-x-bad" title="contrary to the expected ${esc(i.expectCode)}">≠ ${esc(i.expectCode)}</span>`;
  if (i.outcome === "weaker") return `<span class="st-x st-x-less" title="less information than expected">expected ${esc(i.expectCode)}</span>`;
  if (i.outcome === "stronger") return `<span class="st-x st-x-more" title="more information than expected (expected ${esc(i.expectCode)})">+ over ${esc(i.expectCode)}</span>`;
  return "";
}
// `x`: a problem name (looked up in `statusOf`) or a status object as above. `opts.chip: false`
// leaves out the expectation chip.
function statusBadge(x, opts) {
  const i = statusInfo(typeof x === "string" ? statusOf.get(x) : x);
  if (!i) return "";
  const cls = ["st", i.cls ? "st-" + i.cls : "", i.dep ? "st-dep" : "", i.open ? "st-open" : ""].filter(Boolean).join(" ");
  const chip = opts && opts.chip === false ? "" : expectationChip(i);
  const marks = (i.expectedOpen ? `<span class="st-x" title="expected to stay open: ${esc(i.expectedOpen.reason)}">${esc(i.expectedOpen.reason)}</span>` : "");
  return `<span class="st-wrap"><span class="${cls}" data-code="${esc(i.stored)}" data-display="${esc(i.code)}" data-outcome="${i.outcome}" role="img" aria-label="${esc(i.title)}" title="${esc(i.title)}">` +
    `${esc(i.code)}</span>${chip}${marks}</span>`;
}
function verdictBadge(p) { const b = statusBadge(p); return b ? " " + b : ""; }

// A modal dialog (the native <dialog>: focus moves in, Escape closes, focus returns). `body` is
// HTML; `actions` are [label, fn] pairs shown as buttons (fn(dialog) may return false to keep it
// open). Returns { el, close }.
function dialog({ title, body, actions, onClose }) {
  const d = document.createElement("dialog");
  const id = "dlg-" + Math.random().toString(36).slice(2);
  d.className = "dlg";
  d.setAttribute("aria-labelledby", id);
  d.innerHTML = `<div class="dlg-head"><h2 id="${id}">${esc(title)}</h2>` +
    '<button type="button" class="dlg-x" aria-label="Close">×</button></div>' +
    `<div class="dlg-body">${body}</div>` +
    (actions && actions.length ? '<div class="dlg-actions">' + actions.map(([l], i) => `<button type="button" data-i="${i}">${esc(l)}</button>`).join("") + "</div>" : "");
  const back = document.activeElement;
  const close = () => { if (d.open) d.close(); };
  d.addEventListener("close", () => {
    d.remove();
    if (back && back.isConnected && typeof back.focus === "function") back.focus();
    if (onClose) onClose();
  });
  d.querySelector(".dlg-x").addEventListener("click", close);
  d.addEventListener("click", (e) => { if (e.target === d) close(); });   // the backdrop
  for (const b of d.querySelectorAll(".dlg-actions button")) b.addEventListener("click", async () => {
    if ((await actions[+b.dataset.i][1]({ el: d, close })) !== false) close();
  });
  document.body.appendChild(d);
  d.showModal();
  return { el: d, close };
}

// ---------- byte viewer ----------
// `viewer(bytes, meta)` renders at most `meta.limit` bytes (default 64 KiB) of an untrusted file
// as text or hex, with the views that accept it (`VIEWERS`, extended with `registerViewer`).
// meta: { name, total (the file's length, when more than `bytes`), lang (e.g. "wat"), limit }.
// Returns { html, init(container) }: `init` wires the view buttons inside `container`.
const VIEWER_LIMIT = 65536;
const VIEWERS = [];
function registerViewer(v) {
  if (!v || !v.id || typeof v.render !== "function") throw new Error("registerViewer: needs id and render");
  if (VIEWERS.some((w) => w.id === v.id)) throw new Error(`registerViewer: ${v.id} is registered twice`);
  VIEWERS.push({ id: v.id, title: v.title || v.id, accepts: v.accepts || (() => true), rank: v.rank || 0, render: v.render });
}
// Whether the bytes read as text: valid UTF-8 without NUL or other C0 controls besides tab, LF, CR.
// A cut file may end inside a character: then up to 3 trailing bytes are not checked.
function looksText(bytes, cut) {
  const ok = (b) => { try { new TextDecoder("utf-8", { fatal: true }).decode(b); return true; } catch (e) { return false; } };
  if (!ok(bytes) && !(cut && [1, 2, 3].some((k) => ok(bytes.subarray(0, bytes.length - k))))) return false;
  for (const b of bytes) if (b < 32 && b !== 9 && b !== 10 && b !== 13) return false;
  return true;
}
function textOf(bytes) { return new TextDecoder("utf-8").decode(bytes); }
function hexDump(bytes) {
  const lines = [];
  for (let o = 0; o < bytes.length; o += 16) {
    const row = bytes.subarray(o, o + 16);
    const hex = [...row].map((b) => b.toString(16).padStart(2, "0")).join(" ");
    const asc = [...row].map((b) => b >= 32 && b < 127 ? String.fromCharCode(b) : ".").join("");
    lines.push(o.toString(16).padStart(8, "0") + "  " + hex.padEnd(47) + "  " + asc);
  }
  return esc(lines.join("\n"));
}
registerViewer({ id: "text", title: "Text", rank: 1, accepts: (b, m) => looksText(b, m.cut), render: (b) => esc(textOf(b)) });
registerViewer({ id: "hex", title: "Hex", rank: 0, render: (b) => hexDump(b) });
function viewer(bytes, meta) {
  meta = meta || {};
  const limit = meta.limit || VIEWER_LIMIT;
  const shown = bytes.subarray(0, limit), total = meta.total == null ? bytes.length : meta.total;
  meta = Object.assign({}, meta, { cut: shown.length < total });
  const views = VIEWERS.filter((v) => v.accepts(shown, meta)).sort((a, b) => b.rank - a.rank);
  const id = "vw-" + Math.random().toString(36).slice(2);
  const html = `<div class="viewer" id="${id}"><div class="controls" role="group" aria-label="view as">` +
    views.map((v, i) => `<button type="button" data-v="${esc(v.id)}" aria-pressed="${i === 0}">${esc(v.title)}</button>`).join("") +
    `<span class="muted">${shown.length < total ? `the first ${shown.length} of ${total} bytes` : `${total} bytes`}</span></div>` +
    `<pre class="code" tabindex="0">${views[0].render(shown, meta)}</pre></div>`;
  const init = (root) => {
    const el = (root || document).querySelector("#" + id);
    if (!el) return;
    for (const b of el.querySelectorAll("button[data-v]")) b.addEventListener("click", () => {
      const v = views.find((w) => w.id === b.dataset.v);
      el.querySelector("pre").innerHTML = v.render(shown, meta);
      for (const o of el.querySelectorAll("button[data-v]")) o.setAttribute("aria-pressed", String(o === b));
    });
  };
  return { html, init };
}

// WebAssembly text: comments, strings, keywords, types, $names and numbers. The output is built
// from escaped pieces only.
const WAT_TYPES = new Set(["i32", "i64", "f32", "f64", "v128", "funcref", "externref", "anyref", "eqref", "i31ref",
  "structref", "arrayref", "exnref", "nullref", "nullfuncref", "nullexternref", "ref", "null", "mut"]);
const WAT_DECLS = new Set(["module", "component", "core", "func", "param", "result", "local", "global", "table", "memory", "type",
  "import", "export", "elem", "data", "start", "offset", "item", "declare", "rec", "sub", "final", "struct", "array", "field",
  "tag", "instance", "alias", "canon", "lift", "lower", "with", "record", "variant", "list", "tuple", "flags", "enum", "option",
  "own", "borrow", "resource", "string", "then", "else", "block", "loop", "if", "try_table", "catch", "catch_all"]);
function highlightWat(src) {
  const re = /(;;[^\n]*|\(;[\s\S]*?;\))|("(?:[^"\\\n]|\\.)*")|(\$[^\s()";]+)|([+-]?(?:0x[0-9a-fA-F_.pP+-]+|\d[\d_]*(?:\.[\d_]*)?(?:[eE][+-]?\d+)?|inf|nan(?::0x[0-9a-fA-F]+)?)(?![\w.$]))|([a-z][\w.]*(?:=[^\s()]*)?)/g;
  let out = "", last = 0, m;
  while ((m = re.exec(src))) {
    out += esc(src.slice(last, m.index));
    const [t] = m;
    const cls = m[1] ? "c" : m[2] ? "s" : m[3] ? "n" : m[4] ? "d" : WAT_TYPES.has(t) ? "t" : WAT_DECLS.has(t) ? "k" : /^[a-z0-9]+\.[a-z0-9_.]+$|^(?:unreachable|nop|br|br_if|br_table|return|call|call_indirect|drop|select|end|throw|rethrow|return_call|return_call_indirect)$/.test(t) ? "i" : "";
    out += cls ? `<span class="hl-${cls}">${esc(t)}</span>` : esc(t);
    last = m.index + t.length;
  }
  return out + esc(src.slice(last));
}
registerViewer({ id: "wat", title: "WAT", rank: 2, accepts: (b, m) => m.lang === "wat" || /\.wat$/i.test(m.name || ""),
  render: (b) => highlightWat(textOf(b)) });
