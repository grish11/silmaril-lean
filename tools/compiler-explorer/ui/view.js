// Pure functions of the compiler explorer's view: no DOM. Tested by tests/view.test.mjs.

/** Byte offset [start, end) of each line of a text (as UTF-8 bytes), lines numbered from 1. */
export function lineOffsets(text) {
  const enc = new TextEncoder();
  const out = [];
  let pos = 0;
  for (const line of text.split("\n")) {
    const n = enc.encode(line).length;
    out.push([pos, pos + n]);
    pos += n + 1;
  }
  if (text.endsWith("\n")) out.pop();
  return out;
}

const overlaps = (a0, a1, b0, b1) => (a0 < b1 && b0 < a1) || (a0 === a1 && b0 <= a0 && a0 < b1);

/** The 1-based display lines a fragment covers. `lines` are the byte ranges of the displayed text;
 * `targetMap` (for the `text-offset` space) lists [offLo, offHi, byteStart, byteEnd] per listing line. */
export function fragmentLines(fragment, lines, targetMap) {
  const out = new Set();
  for (const [lo, hi] of fragment.ranges) {
    if (fragment.space === "bytes") {
      lines.forEach(([s, e], i) => { if (overlaps(lo, hi, s, e)) out.add(i + 1); });
    } else if (fragment.space === "text-offset") {
      for (const [o0, o1, s] of targetMap || []) {
        if (overlaps(lo, hi, o0, o1)) {
          const i = lines.findIndex(([ls]) => ls === s);
          if (i >= 0) out.add(i + 1);
        }
      }
    }
  }
  return [...out].sort((a, b) => a - b);
}

/** Index the edges of one kind: for each side, display line -> edge ids, and edge -> lines.
 * The relation is many-to-many: a line can lie in several edges and an edge spans several lines
 * (on either side, possibly not contiguous). */
export function indexEdges(problem, kind, srcLines, tgtLines) {
  const map = problem.view.target_map;
  const lines = { source: srcLines, target: tgtLines };
  const byLine = { source: new Map(), target: new Map() };
  const edgeLines = new Map();
  for (const e of problem.edges) {
    if (e.kind !== kind) continue;
    const el = { source: new Set(), target: new Set() };
    for (const side of ["source", "target"]) {
      for (const fid of e[side]) {
        const f = problem.fragments[fid];
        if (!f) continue;
        for (const n of fragmentLines(f, lines[side], side === "target" ? map : null)) {
          el[side].add(n);
          if (!byLine[side].has(n)) byLine[side].set(n, []);
          byLine[side].get(n).push(e.id);
        }
      }
    }
    edgeLines.set(e.id, { source: [...el.source].sort((a, b) => a - b), target: [...el.target].sort((a, b) => a - b) });
  }
  return { byLine, edgeLines };
}

/** The obligations attached to an edge (its segment and its C-to-Core point). */
export function edgeObligations(problem, edgeId) {
  return problem.obligations.filter((o) => o.edge === edgeId);
}

/** What a status badge says. Only the server's `proved` is ever shown as proved. */
export function badge(status) {
  const known = {
    proved: ["proved", "a theorem of exactly this statement, checked when Lean built it; read back by the exporter this database ran"],
    claimed: ["claimed", "an exporter result handed in as a file, not run by this database"],
    open: ["open", "stated in Lean, neither proved nor disproved: unknown"],
    unchecked: ["not loaded", "a proof is named but no checked evidence is recorded"],
    unavailable: ["evidence unavailable", "the project database lacks the required row; no theorem was checked"],
    incompatible: ["incompatible evidence", "the project row does not match this problem; no theorem was checked"],
    rejected: ["rejected", "the named proof does not prove this statement"],
    stale: ["stale", "proof or refutation only for another version of these artifacts"],
    refuted: ["disproved", "a theorem of the statement's negation, checked by Lean's kernel"],
    unbound: ["unbound", "a theorem proves it, but the Lean function is not shown to be the target's code"],
    unsupported: ["unsupported", "not stated: no model covers it"],
    passed: ["test passed", "an execution test, not a proof"],
    failed: ["test failed", "an execution test failed"],
  };
  const [label, title] = known[status] || ["unknown", "no status recorded"];
  return { cls: `st-${known[status] ? status : "unknown"}`, label, title };
}

/** Lines of a side not covered by any edge of a kind (optimized away, generated, unattributed). */
export function uncovered(index, side, count, isCode) {
  const out = [];
  for (let n = 1; n <= count; n++) if (isCode(n) && !index.byLine[side].has(n)) out.push(n);
  return out;
}

// ---------- syntax highlighting: tokens, never HTML ----------
// A highlighter returns, per line, a list of [text, class] tokens whose texts concatenate to the
// line exactly; the page inserts each token with textContent, so no text is ever parsed as HTML.

const C_KEYWORDS = new Set(("auto break case char const continue default do double else enum extern float for goto if " +
  "inline int long register restrict return short signed sizeof static struct switch typedef union unsigned void " +
  "volatile while _Bool _Complex _Atomic _Static_assert _Noreturn _Alignas _Alignof _Generic _Thread_local").split(" "));

/** The language of an artifact by its media type. */
export function langOf(media) {
  if (media === "text/x-c") return "c";
  if (media === "text/x-asm" || media === "text/x-objdump") return "asm";
  if (media === "text/x-lisp") return "sexp";
  return "plain";
}

function scan(line, rules) {
  const out = [];
  let i = 0;
  while (i < line.length) {
    let hit = null;
    for (const [re, cls] of rules) {
      re.lastIndex = i;
      const m = re.exec(line);
      if (m && m.index === i && m[0].length) { hit = [m[0], typeof cls === "function" ? cls(m[0]) : cls]; break; }
    }
    if (!hit) hit = [line[i], ""];
    if (out.length && out[out.length - 1][1] === hit[1]) out[out.length - 1][0] += hit[0];
    else out.push(hit);
    i += hit[0].length;
  }
  return out;
}

const C_RULES = [
  [/\/\/.*/y, "tok-comment"], [/\/\*.*?(\*\/|$)/y, "tok-comment"],
  [/"(\\.|[^"\\])*"?/y, "tok-string"], [/'(\\.|[^'\\])*'?/y, "tok-string"],
  [/^\s*#\s*\w+/y, "tok-preproc"],
  [/0[xX][0-9a-fA-F]+[uUlL]*|\d+(\.\d+)?([eE][+-]?\d+)?[uUlLfF]*/y, "tok-number"],
  [/[A-Za-z_]\w*/y, (w) => (C_KEYWORDS.has(w) ? "tok-keyword" : "")],
];
const ASM_RULES = [
  [/#.*/y, "tok-comment"], [/^\s*[0-9a-f]+:(?=\t)/y, "tok-address"], [/^\s*[.\w$]+:/y, "tok-label"],
  [/(?<=\t)([0-9a-f]{2} )+(?=\s*\t)/y, "tok-bytes"],
  [/\.[A-Za-z_][\w.]*/y, "tok-directive"], [/%[a-z0-9]+/y, "tok-register"],
  [/\$?-?0x[0-9a-fA-F]+|\$?-?\d+/y, "tok-number"], [/"(\\.|[^"\\])*"?/y, "tok-string"],
  [/<[^>\n]*>/y, "tok-label"],
  [/(?<=^\s+|\t)[A-Za-z][A-Za-z0-9]*(?=\s|$)/y, "tok-keyword"],
];
const SEXP_RULES = [
  [/"(\\.|[^"\\])*"?/y, "tok-string"], [/\$[A-Za-z_]+/y, "tok-keyword"], [/-?\d+/y, "tok-number"],
  [/[()]/y, "tok-punct"],
];

/** Tokens of one line of a language. */
export function highlightLine(line, lang) {
  if (lang === "c") return scan(line, C_RULES);
  if (lang === "asm") return scan(line, ASM_RULES);
  if (lang === "sexp") return scan(line, SEXP_RULES);
  return [[line, ""]];
}

/** Tokens of every line of a text: C block comments carry over lines. */
export function highlightText(text, lang) {
  const out = [];
  let open = false;
  for (const line of text.split("\n")) {
    if (lang === "c" && open) {
      const end = line.indexOf("*/");
      if (end < 0) { out.push([[line, "tok-comment"]]); continue; }
      const rest = highlightLine(line.slice(end + 2), lang);
      out.push([[line.slice(0, end + 2), "tok-comment"], ...rest.filter((t) => t[0].length)]);
      open = opensComment(line.slice(end + 2));
      continue;
    }
    out.push(highlightLine(line, lang));
    open = lang === "c" && opensComment(line);
  }
  return out;
}

// Whether a line of C leaves a block comment open (strings and line comments respected).
function opensComment(line) {
  const toks = highlightLine(line, "c");
  const last = toks[toks.length - 1];
  return !!last && last[1] === "tok-comment" && last[0].startsWith("/*") && !last[0].endsWith("*/");
}

export function includeRows(env) {
  const files = env.files.map((file) => ({
    label: file.name.split("/").at(-1), path: file.name,
    main: file.artifact === "source", size: file.size, sha256: file.sha256,
  }));
  if (!env.trace) return files;
  const byPath = new Map(files.map((file) => [file.path, file]));
  const rows = new Map();
  env.trace.occurrences.forEach((event, index) => {
    const file = byPath.get(event.resolved);
    const kind = event.directive === "implicit" ? "implicit" : event.parent === null ? "direct" : "indirect";
    const label = event.operand?.slice(1, -1) ?? file?.label ?? "(unknown)";
    const key = JSON.stringify([label, event.resolved, kind]);
    if (!rows.has(key)) rows.set(key, { ...file, label, path: event.resolved, kind, events: [] });
    rows.get(key).events.push({ ...event, index });
  });
  return [...files.filter((file) => file.main), ...rows.values()];
}

export function prettySexp(text, width = 88) {
  const lex = /\s+|[()]|"(?:\\[\s\S]|[^"\\])*"|;[^\r\n]*|#\||(?:(?!#\||\|#)[^\s();"])+/y;
  const block = /#\||\|#/g;
  const roots = [];
  const stack = [];
  let offset = 0;
  while (offset < text.length) {
    lex.lastIndex = offset;
    const match = lex.exec(text);
    if (!match) return null;
    let token = match[0];
    const start = offset;
    offset = lex.lastIndex;
    if (/^\s/.test(token)) continue;
    const parent = stack.at(-1);
    if (token === ")") {
      if (!parent) return null;
      stack.pop();
      const outer = stack.at(-1);
      if (outer) outer.flat += parent.flat;
      continue;
    }
    const comment = token.startsWith(";") || token === "#|";
    if (token === "#|") {
      block.lastIndex = offset;
      let depth = 1;
      while (depth) {
        const delimiter = block.exec(text);
        if (!delimiter) return null;
        depth += delimiter[0] === "#|" ? 1 : -1;
      }
      offset = block.lastIndex;
      token = text.slice(start, offset);
    }
    const list = token === "(";
    const node = list ? { children: [], flat: 2 } : {
      token, comment, flat: comment || /[\r\n]/.test(token) ? Infinity : token.length,
    };
    const siblings = parent ? parent.children : roots;
    if (parent) parent.flat += (siblings.length ? 1 : 0) + (list ? 0 : node.flat);
    siblings.push(node);
    if (list) stack.push(node);
  }
  if (stack.length || roots.filter((node) => !node.comment).length !== 1) return null;

  const output = [];
  let column = 0;
  const append = (piece) => {
    output.push(piece);
    const lastBreak = piece.lastIndexOf("\n");
    column = lastBreak < 0 ? column + piece.length : piece.length - lastBreak - 1;
  };
  const indent = (depth) => "\n" + " ".repeat(Math.min(2 * depth, 40));
  const pending = roots.map((node, index) => ({ node, depth: 0, before: index ? "\n" : "" })).reverse();
  while (pending.length) {
    const { node, depth, before = "", flat = false } = pending.pop();
    if (before) append(before);
    if (!node.children) {
      append(node.token);
      continue;
    }
    append("(");
    const inline = flat || !node.children.length || column - 1 + node.flat <= width;
    pending.push({ node: { token: ")" }, depth, before: inline ? "" : indent(depth) });
    for (let index = node.children.length - 1; index >= 0; index--) {
      const child = node.children[index];
      const head = index === 0 && !child.children && !child.comment;
      pending.push({ node: child, depth: depth + 1, flat: inline,
        before: inline ? (index ? " " : "") : (head ? "" : indent(depth + 1)) });
    }
  }
  return output.join("");
}

export function stageTrust(problem, stage, evidence) {
  const bound = !problem.lean?.bindings?.length || problem.bindings_checked;
  if (stage.trust === "verified" && (!bound || evidence?.status !== "proved")) return "unchecked";
  if (stage.trust === "evaluated" && stage.model && !problem.bindings_checked) return "unchecked";
  return stage.trust;
}
