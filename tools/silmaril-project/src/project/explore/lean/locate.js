// ---------- Lean source: finding a declaration by a text search ----------
// The fallback of the source view when the database records no `decl_locations` row (Lean's
// `DeclarationRanges`) for a declaration. It reads the tokens of `LeanTokenize`, so comments and
// strings never match, and finds:
//   * declarations (`theorem`, `def`, `instance`, `structure`, … after modifiers, `@[…]`
//     attributes and a doc comment, on the same or preceding lines), named in the current
//     `namespace`s (`_root_.` escapes them); «escaped» names compare without the guillemets;
//   * `silmaril <command> <name>` commands (instance, problem, group, language, format, value, …),
//     whose name is the problem or object they register, as written or inside the namespaces;
//   * the targets of `@[answers "p" …]`, `@[solves "p"]`, `@[refutes "p"]` (matched only against
//     `aliases`, the names the caller says the declaration may stand for).
// `locateLeanDecl(text, decl, { tokens, aliases })` returns the best match or null:
//   { startLine, endLine, selLine, selCol, selEndCol, name, kind, match }
// with `startLine` the first line of the declaration's header (doc comment, attributes), `sel*` the
// position of its name (1-based line, 0-based code point columns, as in Lean), `endLine` an
// estimate: the line before the next command at the declaration's column or left of it (or before
// a line at that column after a blank line), without trailing blank and comment lines. `match` is
// "name" (the full name matched), "alias", "suffix" (one name is a dotted suffix of the other) or
// "last" (only the last component matched): a text search is never exact.
const LeanLocate = (() => {
  "use strict";
  const T = typeof LeanTokenize !== "undefined" ? LeanTokenize : require("./tokenize.js");
  const ANSWER_ATTRS = new Set(["answers", "solves", "refutes"]);
  // A dotted name's components without guillemets; Lean's private prefix dropped.
  function nameParts(name) {
    let s = String(name || "");
    const priv = s.match(/^_private\.(?:[^.]+\.)*?0\.(.+)$/);
    if (priv) s = priv[1];
    const parts = [];
    let cur = "", inG = false;
    for (const ch of s) {
      if (ch === "«" && !inG) inG = true;
      else if (ch === "»" && inG) inG = false;
      else if (ch === "." && !inG) { parts.push(cur); cur = ""; }
      else cur += ch;
    }
    parts.push(cur);
    return parts[0] === "_root_" ? parts.slice(1) : parts;
  }
  const same = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
  const endsWith = (a, b) => b.length <= a.length && b.every((x, i) => x === a[a.length - b.length + i]);
  const width = (s) => [...s].length;
  const SKIP = new Set(["whitespace", "comment"]);

  // Every named or anonymous declaration and `silmaril` command of `tokens`, in order.
  function declarations(tokens) {
    // significant tokens, each with whether it is the first on its line
    const sig = [];
    let first = true;
    for (const t of tokens) {
      if (t.type === "whitespace") { if (t.text.includes("\n")) first = true; continue; }
      if (t.type === "comment") continue;
      sig.push(Object.assign({ first }, t));
      first = false;
    }
    // lines holding code (not only comments or blanks), and blank lines
    const lines = tokens.length ? tokens[tokens.length - 1].line + (tokens[tokens.length - 1].text.match(/\n/g) || []).length : 0;
    const code = new Uint8Array(lines + 2), blank = new Uint8Array(lines + 2).fill(1);
    for (const t of tokens) {
      if (t.type === "whitespace") continue;
      const nl = (t.text.match(/\n/g) || []).length;
      for (let l = t.line; l <= t.line + nl; l++) { blank[l] = 0; if (t.type !== "comment" && t.type !== "doc-comment") code[l] = 1; }
    }
    const isCommandStart = (t) => (t.type === "command" && t.text !== "deriving") || t.type === "modifier" ||
      (t.type === "attribute" && t.text === "@[") || t.type === "doc-comment";
    const out = [], ns = [];
    for (let k = 0; k < sig.length; k++) {
      const t = sig[k];
      if (t.type !== "command") continue;
      const next = sig[k + 1];
      if (t.text === "namespace" && next) { ns.push(nameParts(next.text)); continue; }
      if (t.text === "section") { ns.push([]); continue; }
      if (t.text === "end") { ns.pop(); continue; }
      let kind = null, nameTok = null;
      if (t.text === "silmaril" && next && next.type === "command") {
        kind = "silmaril " + next.text;
        if (sig[k + 2] && sig[k + 2].type === "decl-name") nameTok = sig[k + 2];
      } else if (T.DECLS.has(t.text) && !(sig[k - 1] && sig[k - 1].type === "command" && sig[k - 1].text === "silmaril")) {
        if (t.text === "class" && next && next.text === "inductive") continue;   // `class inductive`: the second keyword
        kind = t.text;
        if (next && next.type === "decl-name") nameTok = next;
      } else continue;
      // the header: modifiers, attributes and a doc comment before the keyword
      let h = k, targets = [];
      for (;;) {
        const p = sig[h - 1];
        if (!p) break;
        if (p.type === "modifier") { h--; continue; }
        if (p.type === "doc-comment") { h--; break; }
        if (p.type === "attribute" && p.text === "]") {
          let a = h - 1;
          while (a > 0 && !(sig[a].type === "attribute" && sig[a].text === "@[")) a--;
          for (let b = a + 1; b < h - 1; b++) {
            if (sig[b].type === "attribute" && ANSWER_ATTRS.has(sig[b].text) && sig[b + 1] && sig[b + 1].type === "string") {
              targets.push(sig[b + 1].text.slice(1, -1));
            }
          }
          h = a; continue;
        }
        break;
      }
      const head = sig[h], col = head.col;
      // the end: before the next command at or left of the header's column, or before a line at
      // that column after a blank line
      let stop = lines + 1;
      for (let m = k + 1; m < sig.length; m++) {
        const u = sig[m];
        if (!u.first || u.col > col) continue;
        if (isCommandStart(u) || u.text.startsWith("#") || blank[u.line - 1]) { stop = u.line; break; }
      }
      const selLine = nameTok ? nameTok.line : t.line;
      let end = stop - 1;
      while (end > selLine && !code[end]) end--;
      const parts = nameTok ? nameParts(nameTok.text) : null;
      const qualified = parts && (nameTok.text.startsWith("_root_.") ? parts : [].concat(...ns, parts));
      out.push({ kind, name: nameTok ? nameTok.text : null, parts, qualified, targets, startLine: head.line, endLine: end, selLine,
        selCol: nameTok ? nameTok.col : t.col, selEndCol: nameTok ? nameTok.col + width(nameTok.text) : t.col + width(t.text) });
    }
    return out;
  }

  function locateLeanDecl(text, decl, opts) {
    const o = opts || {};
    const want = nameParts(decl);
    if (!want.length || !want[want.length - 1]) return null;
    const aliases = (o.aliases || []).filter(Boolean).map(String);
    const tokens = o.tokens || T.tokenizeLean(text);
    let best = null, bestScore = 0;
    for (const d of declarations(tokens)) {
      let score = 0, match = null;
      if (d.parts && (same(d.qualified, want) || (d.kind.startsWith("silmaril ") && same(d.parts, want)))) { score = 4; match = "name"; }
      else if (d.targets.some((x) => x === String(decl) || aliases.includes(x)) ||
        (d.parts && aliases.some((a) => same(nameParts(a), d.parts) || same(nameParts(a), d.qualified)))) { score = 3; match = "alias"; }
      else if (d.parts && ((d.qualified.length > 1 && endsWith(want, d.qualified)) || (want.length > 1 && endsWith(d.qualified, want)) ||
        (d.parts.length > 1 && endsWith(want, d.parts)))) { score = 2; match = "suffix"; }
      else if (d.parts && d.parts[d.parts.length - 1] === want[want.length - 1]) { score = 1; match = "last"; }
      if (score > bestScore) { best = Object.assign({}, d, { match }); bestScore = score; }
      if (score === 4) break;
    }
    if (!best) return null;
    const { startLine, endLine, selLine, selCol, selEndCol, name, kind, match } = best;
    return { startLine, endLine, selLine, selCol, selEndCol, name, kind, match };
  }
  return Object.freeze({ locateLeanDecl, declarations, nameParts });
})();
if (typeof module !== "undefined" && module.exports) module.exports = LeanLocate;
