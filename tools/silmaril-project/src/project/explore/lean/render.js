// ---------- Lean source: HTML ----------
// `LeanRender.renderLeanLines(tokens, from, to, { marks })` turns `LeanTokenize` tokens into one
// HTML string per source line `from..to` (1-based, inclusive): every token's text escaped, inside
// `<span class="lt-<type>">` (whitespace bare); a token over several lines (a block comment, a
// string) is cut at its newlines, each piece keeping its class.
//
// Semantic overlays: `marks` are ranges in Lean's coordinates, `{ line, col, endCol, cls, title,
// attrs }` (1-based line, 0-based code point columns, on one line). The renderer cuts the tokens at
// their boundaries and wraps the covered text in `<span class="<cls>" title=…>` (attribute names
// must match [a-z-]+; values are escaped). The source view marks a declaration's name with one.
// This is where a semantic layer plugs in, without changing the tokenizer: Lean's info trees
// (from a language server, or precomputed per declaration next to `decl_locations`) give ranges
// with a type, a docstring and a definition site; they become marks with `title` (hover) and
// `attrs` (`data-def`, …, for go-to-definition), and a page script listens on them.
const LeanRender = (() => {
  "use strict";
  const ESC = { "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" };
  const escape = (s) => String(s).replace(/[&<>"']/g, (c) => ESC[c]);
  const piece = (type, text) => (type === "whitespace" || !text ? escape(text) : `<span class="lt-${type}">${escape(text)}</span>`);
  function open(m) {
    let a = ` class="${escape(m.cls || "lt-mark")}"`;
    if (m.title) a += ` title="${escape(m.title)}"`;
    for (const [k, v] of Object.entries(m.attrs || {})) if (/^[a-z][a-z-]*$/.test(k) && !/^on/.test(k)) a += ` ${k}="${escape(v)}"`;
    return `<span${a}>`;
  }
  function renderLeanLines(tokens, from, to, opts) {
    const marks = new Map();
    for (const m of (opts && opts.marks) || []) {
      if (!(m.endCol > m.col)) continue;
      if (!marks.has(m.line)) marks.set(m.line, []);
      marks.get(m.line).push(m);
    }
    for (const ms of marks.values()) {
      ms.sort((a, b) => a.col - b.col);
      for (let i = ms.length - 1; i > 0; i--) if (ms[i].col < ms[i - 1].endCol) ms.splice(i, 1);   // no overlaps
    }
    const out = [];
    for (let l = from; l <= to; l++) out.push("");
    let line = 0, col = 0;
    // the segments of each line: [col, type, text]
    const segs = new Map();
    for (const t of tokens) {
      line = t.line; col = t.col;
      if (line > to) break;
      const parts = t.text.split("\n");
      for (let p = 0; p < parts.length; p++) {
        if (p > 0) { line++; col = 0; }
        if (line >= from && line <= to && parts[p]) {
          if (!segs.has(line)) segs.set(line, []);
          segs.get(line).push([col, t.type, parts[p]]);
        }
        col += [...parts[p]].length;
      }
    }
    for (let l = from; l <= to; l++) {
      const ss = segs.get(l) || [], ms = marks.get(l) || [];
      let h = "", mi = 0, inMark = null;
      for (const [c0, type, text] of ss) {
        const chars = [...text];
        let c = c0, k = 0;
        while (k < chars.length) {
          if (inMark && c >= inMark.endCol) { h += "</span>"; inMark = null; }
          while (!inMark && mi < ms.length && ms[mi].endCol <= c) mi++;
          if (!inMark && mi < ms.length && ms[mi].col <= c) { inMark = ms[mi++]; h += open(inMark); }
          // the next boundary: the end of the open mark, the start of the next one, or the token's end
          let stop = c0 + chars.length;
          if (inMark) stop = Math.min(stop, inMark.endCol);
          else if (mi < ms.length) stop = Math.min(stop, Math.max(ms[mi].col, c + 1));
          h += piece(type, chars.slice(k, k + stop - c).join(""));
          k += stop - c; c = stop;
        }
      }
      if (inMark) h += "</span>";
      out[l - from] = h;
    }
    return out;
  }
  return Object.freeze({ renderLeanLines, escape });
})();
if (typeof module !== "undefined" && module.exports) module.exports = LeanRender;
