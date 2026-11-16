// ---------- shared components ----------
// Small components every view can use (and `Explorer.ui` exports): links, status badges, a
// modal dialog and a bounded byte viewer. They return HTML strings or wire up elements; every
// piece of text they show is escaped, since names, titles and file contents are untrusted.
function href(kind, key) { return "#/" + kind + "/" + encodeURIComponent(key); }
function link(kind, key, text) { return `<a href="${href(kind, key)}">${esc(text == null ? key : text)}</a>`; }
// A plain tag (`badge("holds")`): the verdict colours of the graph legend.
function badge(v, text) { return v ? `<span class="badge ${esc(v)}">${esc(text || v)}</span>` : ""; }

// Status badges. A problem's summary is an SZS code (THM, OPN, SAT, UNS, CSA, UNK, contingent);
// its verdict (holds/fails/unknown, see the `szs` table) depends on the problem (UNS fails only a
// closed one). The badge shows the code in a neutral style, and marks only what needs attention:
//   bad    the verdict fails and nothing explains it: not the expected status, not deprecated,
//          and not classified as a spec bug or model gap (a finding `error` is bad, and so is an
//          unclassified failure);
//   unmet  an expected status (`problems.expect`) that the summary is not;
//   dep    the problem is deprecated (it stays listed, with its successors on its page).
// What each stored code means here (the `szs` table's codes), and its SZS name. Displayed codes
// are three characters: the stored code itself, except `contingent`, which is shown as NOC.
// SZS's NoConsequence (NOC) is "some interpretations are models of Ax, some models of Ax are
// models of C, and some models of Ax are models of ~C" (https://szs.tptp.org/success), which is
// exactly SAT and CSA together, as `contingent` is defined. The mapping is one-to-one and the
// badge's title always names the stored code, so nothing is lost. (TAU, Tautology, is not used:
// THM, "all models of Ax are models of C", is the status a Lean proof establishes here.)
const SZS_TEXT = { THM: "Theorem: proved", OPN: "Open: no answer yet", SAT: "Satisfiable: an instance holds",
  UNS: "Unsatisfiable: refuted for every argument", CSA: "CounterSatisfiable: a counterexample exists", UNK: "Unknown",
  contingent: "both SAT and CSA hold" };
const SZS_NAME = { THM: "Theorem", OPN: "Open", SAT: "Satisfiable", UNS: "Unsatisfiable", CSA: "CounterSatisfiable", UNK: "Unknown",
  contingent: "NoConsequence" };
const STATUS_DISPLAY = { contingent: "NOC" };
const SZS_SOURCE = "https://szs.tptp.org/success";
// The displayed code of a stored status code (unknown codes are shown as stored, never cut).
function statusCode(code) { return Object.hasOwn(STATUS_DISPLAY, code) ? STATUS_DISPLAY[code] : code; }
// A one-line explanation: displayed code, SZS name, meaning here, and the stored code if it differs.
function statusText(code) {
  const shown = statusCode(code);
  return `${shown}${SZS_NAME[code] ? " (SZS " + SZS_NAME[code] + ")" : ""}: ${SZS_TEXT[code] || "status code"}` +
    (shown !== code ? `; stored as "${code}"` : "");
}
// name -> { summary, verdict, expect, deprecated, finding } (filled by `resolve` and the graph)
let statusOf = new Map();
function statusInfo(s) {
  if (!s || !s.summary) return null;
  const expected = !!s.expect && s.expect === s.summary;
  const benign = s.finding === "spec_bug" || s.finding === "model_gap";
  const cls = s.verdict === "fails" && !expected && !s.deprecated && !benign ? "bad"
    : s.expect && !expected ? "unmet" : s.deprecated ? "dep" : "";
  const why = [statusText(s.summary), `verdict ${s.verdict}`];
  if (s.expect) why.push(expected ? `as expected (${s.expect})` : `expected ${s.expect}`);
  if (s.deprecated) why.push("deprecated" + (s.deprecated === "self" ? "" : ` (through its ${s.deprecated})`));
  if (s.finding) why.push(`finding: ${s.finding}`);
  else if (cls === "bad") why.push("unclassified failure");
  return { code: statusCode(s.summary), stored: s.summary, cls, title: why.join("; ") };
}
// `x`: a problem name (looked up in `statusOf`) or a status object as above.
function statusBadge(x) {
  const i = statusInfo(typeof x === "string" ? statusOf.get(x) : x);
  if (!i) return "";
  const mark = i.cls === "bad" ? "!" : i.cls === "unmet" ? "?" : "";
  return `<span class="st${i.cls ? " st-" + i.cls : ""}" data-code="${esc(i.stored)}" role="img" aria-label="${esc(i.title)}" title="${esc(i.title)}">` +
    `${esc(i.code)}${mark ? `<b aria-hidden="true">${mark}</b>` : ""}</span>`;
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
