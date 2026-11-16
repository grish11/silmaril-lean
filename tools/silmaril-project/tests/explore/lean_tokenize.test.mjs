// The explorer's Lean source layer, in Node (no browser): the tokenizer, the text-search locator
// and the HTML renderer of src/project/explore/lean/ (plain scripts of the page's bundle, loaded
// here as CommonJS modules).
//
//   node --test tools/silmaril-project/tests/explore/lean_tokenize.test.mjs
import { test } from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const here = path.dirname(fileURLToPath(import.meta.url));
const lean = path.join(here, "../../src/project/explore/lean");
const require = createRequire(import.meta.url);
const { tokenizeLean } = require(path.join(lean, "tokenize.js"));
const { locateLeanDecl, nameParts } = require(path.join(lean, "locate.js"));
const { renderLeanLines } = require(path.join(lean, "render.js"));
const repo = path.resolve(here, "../../../..");

const toks = (s) => tokenizeLean(s).filter((t) => t.type !== "whitespace").map((t) => [t.type, t.text]);
const roundTrips = (s) => assert.equal(tokenizeLean(s).map((t) => t.text).join(""), s);
const typeOf = (s, text) => (tokenizeLean(s).find((t) => t.text === text) || {}).type;

test("comments: line, nested block, doc and module doc", () => {
  assert.deepEqual(toks("a -- c /- x\nb"), [["name", "a"], ["comment", "-- c /- x"], ["name", "b"]]);
  assert.deepEqual(toks("/- a /- b -/ c -/ x"), [["comment", "/- a /- b -/ c -/"], ["name", "x"]]);
  assert.deepEqual(toks("/-- doc /- in -/ -/ def f := 1"), [["doc-comment", "/-- doc /- in -/ -/"], ["command", "def"], ["decl-name", "f"], ["operator", ":="], ["number", "1"]]);
  assert.deepEqual(toks("/-! # Module\n-- not a comment start\n-/"), [["doc-comment", "/-! # Module\n-- not a comment start\n-/"]]);
  assert.equal(typeOf('-- "a\nb', "b"), "name");
});

test("strings: escapes, interpolation, raw", () => {
  assert.deepEqual(toks('"a\\"b\\\\" x'), [["string", '"a\\"b\\\\"'], ["name", "x"]]);
  assert.deepEqual(toks('s!"a{x + "}"}b\\{c" y'), [["keyword", "s!"], ["string", '"'], ["string", "a"], ["punctuation", "{"], ["name", "x"],
    ["operator", "+"], ["string", '"}"'], ["punctuation", "}"], ["string", 'b\\{c"'], ["name", "y"]]);
  assert.deepEqual(toks('s!"{ {a := 1}.a }"'), [["keyword", "s!"], ["string", '"'], ["string", ""], ["punctuation", "{"], ["punctuation", "{"], ["name", "a"], ["operator", ":="],
    ["number", "1"], ["punctuation", "}"], ["operator", "."], ["name", "a"], ["punctuation", "}"], ["string", '"']].filter((t) => t[1] !== ""));
  assert.deepEqual(toks('r#"a "quoted" b"# r"x"'), [["string", 'r#"a "quoted" b"#'], ["string", 'r"x"']]);
  assert.equal(typeOf('"-- not a comment"', '"-- not a comment"'), "string");
});

test("chars and primes", () => {
  assert.deepEqual(toks("'a' '\\n' '\\x41' '\\u{3bb}' 'λ'"), [["char", "'a'"], ["char", "'\\n'"], ["char", "'\\x41'"], ["char", "'\\u{3bb}'"], ["char", "'λ'"]]);
  assert.deepEqual(toks("x' f'' (x':ℕ)"), [["name", "x'"], ["name", "f''"], ["punctuation", "("], ["name", "x'"], ["operator", ":"], ["name", "ℕ"], ["punctuation", ")"]]);
  assert.deepEqual(toks("a'b' = c"), [["name", "a'b'"], ["operator", "="], ["name", "c"]]);
});

test("names: dotted, «escaped», Unicode, name literals", () => {
  assert.deepEqual(toks("Foo.bar.«baz qux».x₁ αβ.γ _root_.Nat get! p?"), [["name", "Foo.bar.«baz qux».x₁"], ["name", "αβ.γ"], ["name", "_root_.Nat"], ["name", "get!"], ["name", "p?"]]);
  assert.deepEqual(toks("`foo ``Bar.baz `(x)"), [["name", "`foo"], ["name", "``Bar.baz"], ["operator", "`"], ["punctuation", "("], ["name", "x"], ["punctuation", ")"]]);
  assert.deepEqual(toks("h.1 h.2.1"), [["name", "h"], ["operator", "."], ["number", "1"], ["name", "h"], ["operator", "."], ["number", "2.1"]]);
  assert.deepEqual(toks("def «utf-8 text» := 0"), [["command", "def"], ["decl-name", "«utf-8 text»"], ["operator", ":="], ["number", "0"]]);
});

test("Unicode operators and binders", () => {
  assert.deepEqual(toks("∀ x, ∃ y, x ≤ y → y ↔ ¬z ∘ f ×ᵤ g ⟨a, b⟩ λ t ↦ t"), [["keyword", "∀"], ["name", "x"], ["punctuation", ","], ["keyword", "∃"], ["name", "y"],
    ["punctuation", ","], ["name", "x"], ["operator", "≤"], ["name", "y"], ["operator", "→"], ["name", "y"], ["operator", "↔"], ["operator", "¬"], ["name", "z"],
    ["operator", "∘"], ["name", "f"], ["operator", "×ᵤ"], ["name", "g"], ["punctuation", "⟨"], ["name", "a"], ["punctuation", ","], ["name", "b"],
    ["punctuation", "⟩"], ["keyword", "λ"], ["name", "t"], ["operator", "↦"], ["name", "t"]]);
  assert.deepEqual(toks("fun x => x |>.foo <| a"), [["keyword", "fun"], ["name", "x"], ["operator", "=>"], ["name", "x"], ["operator", "|>."], ["name", "foo"], ["operator", "<|"], ["name", "a"]]);
  assert.deepEqual(toks("a--b"), [["name", "a"], ["comment", "--b"]]);
  assert.deepEqual(toks("a:=/-c-/b"), [["name", "a"], ["operator", ":="], ["comment", "/-c-/"], ["name", "b"]]);
});

test("numbers", () => {
  assert.deepEqual(toks("42 0x1F 0b1010 0o17 3.14 1e10 2.5e-3 1_000"), [["number", "42"], ["number", "0x1F"], ["number", "0b1010"], ["number", "0o17"],
    ["number", "3.14"], ["number", "1e10"], ["number", "2.5e-3"], ["number", "1_000"]]);
  assert.deepEqual(toks("[1..5]"), [["punctuation", "["], ["number", "1"], ["operator", ".."], ["number", "5"], ["punctuation", "]"]]);
});

test("commands, modifiers, attributes, sorry", () => {
  assert.deepEqual(toks("#check Nat.succ\n#eval 1"), [["command", "#check"], ["name", "Nat.succ"], ["command", "#eval"], ["number", "1"]]);
  assert.deepEqual(toks('@[answers "p.q" thm, simp] public noncomputable theorem t : True := by sorry'), [["attribute", "@["], ["attribute", "answers"],
    ["string", '"p.q"'], ["name", "thm"], ["punctuation", ","], ["attribute", "simp"], ["attribute", "]"], ["modifier", "public"], ["modifier", "noncomputable"],
    ["command", "theorem"], ["decl-name", "t"], ["operator", ":"], ["name", "True"], ["operator", ":="], ["keyword", "by"], ["sorry", "sorry"]]);
  assert.deepEqual(toks("@[local simp] lemma l := admit"), [["attribute", "@["], ["modifier", "local"], ["attribute", "simp"], ["attribute", "]"], ["command", "lemma"],
    ["decl-name", "l"], ["operator", ":="], ["sorry", "admit"]]);
  assert.deepEqual(toks("@[foo [1, 2]] def x"), [["attribute", "@["], ["attribute", "foo"], ["punctuation", "["], ["number", "1"], ["punctuation", ","], ["number", "2"],
    ["punctuation", "]"], ["attribute", "]"], ["command", "def"], ["decl-name", "x"]]);
  assert.deepEqual(toks("silmaril instance a.b (expect := OPN)").slice(0, 3), [["command", "silmaril"], ["command", "instance"], ["decl-name", "a.b"]]);
  assert.deepEqual(toks("silmaril group g.h").slice(0, 3), [["command", "silmaril"], ["command", "group"], ["decl-name", "g.h"]]);
  assert.deepEqual(toks("instance : Inhabited Nat := ⟨0⟩").slice(0, 2), [["command", "instance"], ["operator", ":"]]);
  assert.deepEqual(toks("namespace A.B\nend A.B"), [["command", "namespace"], ["name", "A.B"], ["command", "end"], ["name", "A.B"]]);
  assert.equal(typeOf("x.sorry_free", "x.sorry_free"), "name");
});

test("unterminated input at the end: no throw, no lost text", () => {
  for (const s of ["/- open", "/- a /- b -/", "/-- doc", '"abc', '"abc\\', 's!"a{', 's!"a{x', "'", "«open", "r#\"x\"", "@[simp", "x.", "a /-"]) {
    roundTrips(s);
  }
  assert.equal(tokenizeLean("x /- open").at(-1).type, "error");
  assert.equal(tokenizeLean('x "open').at(-1).type, "error");
  assert.equal(tokenizeLean("«open x").at(0).type, "error");
  assert.deepEqual(tokenizeLean(""), []);
});

test("positions are Lean's: 1-based lines, 0-based code point columns", () => {
  const t = tokenizeLean("/- α\n β -/ def 𝓒x := 'a'\n  x");
  const at = (text) => { const k = t.find((x) => x.text === text); return [k.line, k.col]; };
  assert.deepEqual(at("def"), [2, 6]);
  assert.deepEqual(at("𝓒x"), [2, 10]);
  assert.deepEqual(at(":="), [2, 13]);
  assert.deepEqual(at("x"), [3, 2]);
});

test("round trip and no errors on the repository's Lean files", () => {
  const files = [];
  const walk = (d) => {
    for (const e of fs.readdirSync(d, { withFileTypes: true })) {
      if (e.name.startsWith(".")) continue;
      const p = path.join(d, e.name);
      if (e.isDirectory()) walk(p); else if (p.endsWith(".lean")) files.push(p);
    }
  };
  walk(path.join(repo, "examples/project"));
  const ex = files.splice(0);
  walk(path.join(repo, "Silmaril"));
  const lib = files.sort();
  // every example file, and every 7th library file (all of them take some 20 s)
  const all = [...ex, ...lib.filter((_, i) => i % 7 === 0)];
  assert.ok(ex.length > 10 && lib.length > 100, `found ${ex.length} example and ${lib.length} library files`);
  for (const f of all) {
    const s = fs.readFileSync(f, "utf8"), t = tokenizeLean(s);
    assert.equal(t.map((x) => x.text).join(""), s, `round trip of ${f}`);
    const e = t.find((x) => x.type === "error");
    assert.equal(e, undefined, `${f}:${e && e.line}: error token ${e && JSON.stringify(e.text.slice(0, 40))}`);
  }
});

test("locate: a silmaril command's problem (json_format_eq_json)", () => {
  const text = fs.readFileSync(path.join(repo, "examples/project/ProjectSelfTest/Languages.lean"), "utf8");
  const line = text.split("\n").findIndex((l) => l.startsWith("silmaril instance silmaril.selftest.languages.json_format_eq_json ")) + 1;
  assert.ok(line > 0);
  const l = locateLeanDecl(text, "silmaril.selftest.languages.json_format_eq_json");
  assert.deepEqual({ ...l }, { startLine: line, endLine: line + 2, selLine: line, selCol: 18, selEndCol: 18 + 47,
    name: "silmaril.selftest.languages.json_format_eq_json", kind: "silmaril instance", match: "name" });
});

const FIXTURE = `module
namespace A.B
/-- the doc -/
@[simp]
def helper : Nat := 1

-- a comment that belongs to the next declaration
@[answers "p.q" thm]
public theorem answer_t :
    helper = 1 := by
  -- inside the proof

  rfl
silmaril instance p.r (expect := OPN)
  (title := "x")
theorem «weird name» : True := trivial
end A.B
theorem helper : True := trivial
private def hidden := 0
`;

test("locate: declarations with headers, multi-line proofs, namespaces, escapes", () => {
  const at = (d, opts) => { const l = locateLeanDecl(FIXTURE, d, opts); return l && [l.startLine, l.endLine, l.selLine, l.match]; };
  assert.deepEqual(at("A.B.helper"), [3, 5, 5, "name"]);   // doc comment and attribute start it
  assert.deepEqual(at("A.B.answer_t"), [8, 13, 9, "name"]);   // through the blank line in the proof, up to the next command
  assert.deepEqual(at("p.r"), [14, 15, 14, "name"]);
  assert.deepEqual(at("A.B.p.r"), [14, 15, 14, "name"]);
  assert.deepEqual(at("A.B.«weird name»"), [16, 16, 16, "name"]);
  assert.deepEqual(at("helper"), [18, 18, 18, "name"]);   // the root one, not A.B.helper
  assert.deepEqual(at("_private.Mod.0.hidden"), [19, 19, 19, "name"]);
  assert.deepEqual(at("p.q", { aliases: ["p.q"] }), [8, 13, 9, "alias"]);
  assert.deepEqual(at("Other.answer_t"), [8, 13, 9, "last"]);
  assert.equal(locateLeanDecl(FIXTURE, "A.B.missing"), null);
  assert.equal(locateLeanDecl(FIXTURE, ""), null);
  // a comment or a string that names it is not a declaration
  assert.equal(locateLeanDecl('-- theorem ghost : True\n/- def ghost -/ def x := "theorem ghost"', "ghost"), null);
  assert.deepEqual(nameParts("A.«b.c».d"), ["A", "b.c", "d"]);
});

test("locate: an answer theorem in the repository, its statement and proof", () => {
  const text = fs.readFileSync(path.join(repo, "examples/project/ProjectSelfTest/Languages.lean"), "utf8"), lines = text.split("\n");
  const l = locateLeanDecl(text, "digits_short_bound");
  assert.ok(l, "found");
  assert.match(lines[l.startLine - 1], /^@\[answers "silmaril\.selftest\.languages\.digits_short_bound" thm\]$/);
  assert.match(lines[l.selLine - 1], /^public theorem digits_short_bound :/);
  assert.ok(l.endLine >= l.selLine + 2, "the proof's lines are included");
  assert.ok(!/^\s*$/.test(lines[l.endLine - 1]) && !/^(silmaril|@\[|public|theorem|def)\b/.test(lines[l.endLine - 1]), `ends in the proof: ${lines[l.endLine - 1]}`);
});

test("render: escaped spans per line, multi-line tokens split, marks", () => {
  const t = tokenizeLean('/- <a>\n& -/ theorem x : "s\n\'q\'" := sorry');
  const h = renderLeanLines(t, 1, 3, { marks: [{ line: 2, col: 13, endCol: 14, cls: "lean-sel", title: '<"t">', attrs: { "data-def": "D", onclick: "bad" } }] });
  assert.equal(h.length, 3);
  assert.equal(h[0], '<span class="lt-comment">/- &lt;a&gt;</span>');
  assert.match(h[1], /^<span class="lt-comment">&amp; -\/<\/span> <span class="lt-command">theorem<\/span> <span class="lean-sel" title="&lt;&quot;t&quot;&gt;" data-def="D"><span class="lt-decl-name">x<\/span><\/span> /);
  assert.ok(!h[1].includes("onclick"));
  assert.equal(h[2], '<span class="lt-string">&#39;q&#39;&quot;</span> <span class="lt-operator">:=</span> <span class="lt-sorry">sorry</span>');
  // a mark inside a token cuts it
  const m = renderLeanLines(tokenizeLean("abcdef"), 1, 1, { marks: [{ line: 1, col: 2, endCol: 4, cls: "m" }] })[0];
  assert.equal(m, '<span class="lt-name">ab</span><span class="m"><span class="lt-name">cd</span></span><span class="lt-name">ef</span>');
  // the text of every line is the source line
  const src = fs.readFileSync(path.join(repo, "examples/project/ProjectSelfTest/Languages.lean"), "utf8");
  const n = src.split("\n").length, out = renderLeanLines(tokenizeLean(src), 1, n);
  // the renderer's own tags removed (to a fixpoint), then its entities decoded
  const untag = (x) => { for (let y = null; y !== x;) { y = x; x = x.replace(/<[^>]*>/g, ""); } return x; };
  const plain = (x) => untag(x).replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, '"').replace(/&#39;/g, "'").replace(/&amp;/g, "&");
  assert.deepEqual(out.map(plain), src.split("\n"));
});
