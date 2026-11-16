// ---------- Lean source: tokens ----------
// `LeanTokenize.tokenizeLean(text)` splits Lean 4 source into a flat stream of tokens
// `{ type, text, line, col }` that covers the input exactly: the token texts, concatenated, are
// `text`, whatever it holds (truncated files, unterminated comments or strings: those end in an
// `error` token holding the rest). `line` is 1-based, `col` 0-based in Unicode code points: the
// coordinates of Lean's `DeclarationRanges` and of its info trees.
//
// Types: whitespace, comment (`--`, `/- -/`, nested), doc-comment (`/-- -/`, `/-! -/`), string
// (also raw `r#"…"#` and the literal parts of `s!"…{x}…"`), char, number, name (identifiers,
// dotted, «escaped»; `name literals), decl-name (the name a declaration or a `silmaril`
// command introduces), command (theorem, def, namespace, `#check`, `silmaril` and its subcommand,
// …), modifier (public, private, noncomputable, …), keyword (fun, λ, ∀, by, have, …), attribute
// (`@[`, its attribute names, its closing `]`), sorry (`sorry`, `admit`), operator, punctuation,
// error.
//
// This is a lexical layer only: it knows no types and resolves no names. It is a stream on
// purpose; the semantic layer goes on top of it (see `LeanRender`), never into it.
//
// One script in the page (explore.rs bundles it) and a CommonJS module in Node's tests.
const LeanTokenize = (() => {
  "use strict";
  const DECLS = new Set(["theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
    "coinductive", "axiom", "opaque", "example"]);
  const COMMANDS = new Set([...DECLS, "namespace", "section", "end", "open", "export", "variable", "universe",
    "import", "module", "mutual", "set_option", "attribute", "macro", "macro_rules", "syntax", "elab", "elab_rules",
    "notation", "infix", "infixl", "infixr", "prefix", "postfix", "declare_syntax_cat", "initialize",
    "builtin_initialize", "omit", "include", "deriving", "add_decl_doc", "run_cmd", "run_elab", "run_meta"]);
  const MODIFIERS = new Set(["public", "private", "protected", "noncomputable", "partial", "unsafe", "nonrec",
    "meta", "scoped", "local"]);
  const KEYWORDS = new Set(["fun", "let", "have", "show", "from", "by", "do", "if", "then", "else", "match", "with",
    "at", "in", "where", "calc", "suffices", "obtain", "using", "return", "for", "unless", "mut", "try", "catch",
    "finally", "termination_by", "decreasing_by", "nomatch", "nofun", "Type", "Sort", "Prop", "extends", "forall",
    "exists", "fun", "∀", "∃", "λ", "Π", "Σ"]);
  const SORRY = new Set(["sorry", "admit"]);
  // Names whose `!` makes the string right after it interpolated (`s!"a{x}b"`).
  const INTERPOLATING = new Set(["s!", "m!", "f!"]);
  const PUNCT = new Set([..."()[]{}⟨⟩⦃⦄‹›⟪⟫,;"]);

  // Lean's `isLetterLike` and `isSubScriptAlnum` (Init/Meta), plus other Unicode letters so that
  // no identifier is cut, except λ Π Σ which are binders.
  const letterLike = (c) => (c >= 0x3b1 && c <= 0x3c9 && c !== 0x3bb) || (c >= 0x391 && c <= 0x3a9 && c !== 0x3a0 && c !== 0x3a3) ||
    (c >= 0x3ca && c <= 0x3fb) || (c >= 0x1f00 && c <= 0x1ffe) || (c >= 0x2100 && c <= 0x214f) || (c >= 0x1d49c && c <= 0x1d59f);
  const subAlnum = (c) => (c >= 0x2080 && c <= 0x2089) || (c >= 0x2090 && c <= 0x209c) || (c >= 0x1d62 && c <= 0x1d6a) || c === 0x2c7c;
  const LETTER = /\p{L}/u;
  const isIdStart = (c) => (c >= 0x61 && c <= 0x7a) || (c >= 0x41 && c <= 0x5a) || c === 0x5f || letterLike(c) ||
    (c > 0x7f && c !== 0x3bb && c !== 0x3a0 && c !== 0x3a3 && !subAlnum(c) && LETTER.test(String.fromCodePoint(c)));
  const isIdRest = (c) => isIdStart(c) || (c >= 0x30 && c <= 0x39) || c === 0x27 || c === 0x21 || c === 0x3f || subAlnum(c);
  const isSpace = (ch) => /\s/u.test(ch);

  const CHAR = /'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]{1,6}\}|[^\n])|[^\\'\n])'/uy;
  const NUMBER = /0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|[0-9][0-9_]*(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?/y;
  const RAW = /r(#*)"/y;

  function tokenizeLean(input) {
    const s = String(input), n = s.length, out = [];
    // Frames: code (with the depth of `{` for interpolations and of `[` for attributes) or the
    // literal part of an interpolated string. An explicit stack: no recursion on nesting.
    const stack = [{ kind: "code", braces: 0 }];
    let i = 0, pendingDecl = false, pendingSub = false;
    const cp = (j) => s.codePointAt(j);
    const width = (c) => (c > 0xffff ? 2 : 1);
    const push = (type, text) => { if (text) out.push({ type, text }); };
    // The end of the «escaped» component at j, or -1 (it may not span lines).
    const guillemet = (j) => {
      const l = s.indexOf("\n", j + 1), e = s.slice(j + 1, l < 0 ? n : l).indexOf("»");
      return e < 0 ? -1 : j + 2 + e;
    };
    // The end of an identifier component starting at j (an id start or «), or j.
    const component = (j) => {
      if (s[j] === "«") { const e = guillemet(j); return e < 0 ? j : e; }
      if (j >= n || !isIdStart(cp(j))) return j;
      j += width(cp(j));
      while (j < n && isIdRest(cp(j))) j += width(cp(j));
      return j;
    };
    while (i < n) {
      const top = stack[stack.length - 1];
      if (top.kind === "interp") {
        let j = i;
        while (j < n && s[j] !== '"' && s[j] !== "{") j += s[j] === "\\" ? 2 : 1;
        if (j >= n) { push("error", s.slice(i)); i = n; break; }
        if (s[j] === '"') { push("string", s.slice(i, j + 1)); stack.pop(); i = j + 1; continue; }
        push("string", s.slice(i, j)); push("punctuation", "{");
        stack.push({ kind: "code", braces: 0, interp: true }); i = j + 1; continue;
      }
      const ch = s[i], c = cp(i);
      // whitespace
      if (isSpace(ch)) {
        let j = i + 1;
        while (j < n && isSpace(s[j])) j++;
        push("whitespace", s.slice(i, j)); i = j; continue;
      }
      // comments
      if (ch === "-" && s[i + 1] === "-") {
        let j = s.indexOf("\n", i);
        if (j < 0) j = n;
        push("comment", s.slice(i, j)); i = j; continue;
      }
      if (ch === "/" && s[i + 1] === "-") {
        const doc = s[i + 2] === "-" || s[i + 2] === "!";
        let j = i + (doc ? 3 : 2), depth = 1;
        while (j < n && depth > 0) {
          if (s[j] === "/" && s[j + 1] === "-") { depth++; j += 2; }
          else if (s[j] === "-" && s[j + 1] === "/") { depth--; j += 2; }
          else j++;
        }
        push(depth > 0 ? "error" : doc ? "doc-comment" : "comment", s.slice(i, j)); i = j; continue;
      }
      // strings and chars
      if (ch === '"') {
        let j = i + 1;
        while (j < n && s[j] !== '"') j += s[j] === "\\" ? 2 : 1;
        if (j >= n) { push("error", s.slice(i)); i = n; break; }
        push("string", s.slice(i, j + 1)); pendingDecl = pendingSub = false; i = j + 1; continue;
      }
      if (ch === "r") {
        RAW.lastIndex = i;
        const m = RAW.exec(s);
        if (m) {
          const close = '"' + m[1], e = s.indexOf(close, i + m[0].length);
          if (e < 0) { push("error", s.slice(i)); i = n; break; }
          push("string", s.slice(i, e + close.length)); i = e + close.length; continue;
        }
      }
      if (ch === "'") {
        CHAR.lastIndex = i;
        const m = CHAR.exec(s);
        push(m ? "char" : "operator", m ? m[0] : "'"); i += m ? m[0].length : 1; continue;
      }
      // numbers
      if (c >= 0x30 && c <= 0x39) {
        NUMBER.lastIndex = i;
        const m = NUMBER.exec(s);
        push("number", m[0]); pendingDecl = pendingSub = false; i += m[0].length; continue;
      }
      // names (dotted, «escaped»), keywords, commands
      if (isIdStart(c) || (ch === "«" && guillemet(i) > 0) || (ch === "`" && component(i + 1) > i + 1) ||
          (ch === "`" && s[i + 1] === "`" && component(i + 2) > i + 2)) {
        let j = i;
        if (ch === "`") j += s[i + 1] === "`" ? 2 : 1;
        j = component(j);
        while (s[j] === "." && component(j + 1) > j + 1) j = component(j + 1);
        const t = s.slice(i, j);
        let type = "name";
        if (top.attr && top.expectName && !MODIFIERS.has(t)) { type = "attribute"; top.expectName = false; }
        else if (top.attr && MODIFIERS.has(t)) type = "modifier";
        else if (ch === "`") type = "name";
        else if (SORRY.has(t)) type = "sorry";
        else if (pendingSub) { type = "command"; pendingSub = false; pendingDecl = true; i = j; push(type, t); continue; }
        else if (pendingDecl && !DECLS.has(t) && !MODIFIERS.has(t)) type = "decl-name";
        else if (t === "silmaril" && /^[ \t]+[a-z_]+/.test(s.slice(j, j + 40))) { type = "command"; pendingSub = true; }
        else if (COMMANDS.has(t)) type = "command";
        else if (MODIFIERS.has(t)) type = "modifier";
        else if (KEYWORDS.has(t)) type = "keyword";
        pendingDecl = type === "command" && DECLS.has(t) ? true : type === "modifier" ? pendingDecl : false;
        if (type === "command" && t === "silmaril") pendingSub = true;
        // `s!"…"`: an interpolated string follows
        if (INTERPOLATING.has(t) && s[j] === '"') { push("keyword", t); push("string", '"'); stack.push({ kind: "interp" }); i = j + 1; continue; }
        push(type, t); i = j; continue;
      }
      if (ch === "«") { push("error", "«"); i++; continue; }   // unterminated: Lean rejects it
      // `#check`-style commands
      if (ch === "#" && i + 1 < n && isIdStart(cp(i + 1))) {
        const j = component(i + 1);
        push("command", s.slice(i, j)); pendingDecl = pendingSub = false; i = j; continue;
      }
      // attributes
      if (ch === "@" && s[i + 1] === "[") {
        push("attribute", "@["); stack.push({ kind: "code", braces: 0, attr: true, brackets: 0, expectName: true }); i += 2; continue;
      }
      pendingDecl = pendingSub = false;
      if (PUNCT.has(ch)) {
        if (ch === "{") top.braces++;
        if (ch === "}") {
          if (top.interp && top.braces === 0) { push("punctuation", "}"); stack.pop(); i++; continue; }
          top.braces = Math.max(0, top.braces - 1);
        }
        if (top.attr) {
          if (ch === "[") top.brackets++;
          else if (ch === "]" && top.brackets === 0) { push("attribute", "]"); stack.pop(); i++; continue; }
          else if (ch === "]") top.brackets--;
          else if (ch === "," && top.brackets === 0) top.expectName = true;
        }
        push("punctuation", ch); i++; continue;
      }
      // binders that are single symbols
      if (ch === "∀" || ch === "∃" || ch === "λ" || ch === "Π" || ch === "Σ") { push("keyword", ch); i++; continue; }
      // operators: a run of symbols, up to a comment, a string, a name or punctuation
      let j = i + width(c);
      while (j < n) {
        const d = cp(j), dc = s[j];
        if (isSpace(dc) || isIdStart(d) || (d >= 0x30 && d <= 0x39) || PUNCT.has(dc) || "\"'`«∀∃λΠΣ".includes(dc) ||
            (dc === "-" && s[j + 1] === "-") || (dc === "/" && s[j + 1] === "-") || (dc === "@" && s[j + 1] === "[") ||
            (dc === "#" && j + 1 < n && isIdStart(cp(j + 1)))) break;
        j += width(d);
      }
      push("operator", s.slice(i, j)); i = j;
    }
    // positions: 1-based lines, 0-based code point columns
    let line = 1, col = 0;
    for (const t of out) {
      t.line = line; t.col = col;
      for (const ch of t.text) { if (ch === "\n") { line++; col = 0; } else col++; }
    }
    return out;
  }
  return Object.freeze({ tokenizeLean, DECLS, COMMANDS, MODIFIERS, KEYWORDS });
})();
if (typeof module !== "undefined" && module.exports) module.exports = LeanTokenize;
