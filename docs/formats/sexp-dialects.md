# S-expression text syntaxes over `SExp2`: coverage

Text readers and printers for dotted S-expressions and Lisp-family data syntaxes. Every syntax
reads into the existing dotted tree `SExp2 α` (`Silmaril/Formats/SExp/Basic.lean`) with a named
atom type; no new tree type is introduced. Reading is syntactic: no evaluation, no read-time
effects, no package lookup, no reader extensions.

## Shared machinery

| Piece | Module | Evidence |
| --- | --- | --- |
| Phrase grammar `Gram` (datum, bracketed sequence, dotted tail, prefix) | `SExp/Reader/Defs` | |
| Incremental reader `readPrefix` / `read` / `readAll` over a dialect lexer | `SExp/Reader/Defs` | `readPrefix_iff`, `read_iff` (sound and complete; fuel never the cause of failure) |
| Unambiguity | `SExp/Reader/Thms` | `gram_unique`, `gram_prefix_free` |
| Marker encoding of collections and marker prefixes (`Notation`, `wf`) | `SExp/Reader/Defs` | `wf_of_read` (reader output is `wf`), `gram_tokens` |
| Generic printer and roundtrip from per-dialect lexing laws (`PrintLaws`) | `SExp/Reader/Thms` | `read_print`, `readPrefix_print` |
| Scanners: tokens, quoted literals, integers, rationals, decimal floats | `SExp/Lexical/Defs` | `Proofs/.../Lexical/Basic`: each scanner inverts its printer |

Proper versus recursively proper (#702) is preserved: readers return `SExp2`, improper lists
included; `SExp2.IsProper` / `SExp2.toSExp?` give the proper part. Only POSE, which has no
dotted pairs, always yields proper values.

Collections without a cons-cell meaning are encoded by a **marker atom** at the head of the
spine (`#(a b)` ↦ `cons (atom vector) (a b)`). Marker atoms are never read as ordinary atoms,
so the encoding is injective, and `Notation.wf` is exactly its image (`wf_of_read`,
`read_print`). Abbreviations whose meaning is a list (`'x` is `(quote x)`) read as that list.

## Coverage by syntax

| | Dotted text | Scheme (R7RS-small) | Racket | Common Lisp | Clojure | POSE |
| --- | --- | --- | --- | --- | --- | --- |
| Data type | `DottedSExp.Datum` | `Scheme.Datum` | `Racket.Datum` | `CommonLisp.Datum` | `Clojure.Datum` | `Pose2` |
| Atoms | symbol, string | symbol, boolean, exact ℚ, inexact decimal, char, string | + keyword | symbol (upcased), keyword, `p:s`/`p::s`, `#:s`, ℚ, float (decimal + format), string, char | nil, boolean, integer (+BigInt), float (+BigDecimal), string, char, symbol/keyword with namespace | symbol, string, number |
| Lists, dotted pairs | yes, yes | yes, yes | `()` `[]` `{}`, yes | yes, yes | yes, **no** (`.` is a symbol) | yes, **no** |
| Collections (markers) | – | `#(…)`, `#u8(…)` (elements 0–255, `Valid`) | `#(…)`, box `#&` | `#(…)` | `[…]`, `{…}` (even, no duplicate keys), `#{…}` (no duplicates) | – |
| Abbreviations | – | `'` `` ` `` `,` `,@` → lists | + `#'` `` #` `` `#,` `#,@` | `'` `#'` → lists; `` ` `` `,` `,@` → markers (CLHS 2.4.6) | `'` `@` `#'` `~` `~@` → lists | – |
| Symbol escapes | `\|…\|` | `\|…\|` | `\|…\|` (no escapes inside) | `\`, `\|…\|`, mixed | none (unwritable names) | none |
| Comments | `;` | `;`, nested `#\|…\|#` | `;`, nested `#\|…\|#` | `;`, nested `#\|…\|#` | `;`, commas are whitespace | `;` |
| Roundtrip | `parse?_print` (all data) | `parse?_print` (`wf`, `Valid`) | `parse?_print` (`wf`) | `parse?_print` (`wf`) | `parse?_print` (`wf`, `valid`) | `print?_sound` |
| Grammar | `parse?_iff` | `parse?_iff` | `parse?_iff` | `parse?_iff` | `parse?_iff` | via `Pose.parse?` |
| Examples | `Dotted/Examples` | `Scheme/Examples` | `Racket/Examples` | `CommonLisp/Examples` | `Clojure/Examples` | `Pose2/Examples` |

"Portable S-expressions" is POSE, the `s-expressions/pose` grammar already implemented by
`Silmaril.Formats.Pose` (`SExp/Pose.lean`); it is not Rivest's canonical S-expressions
(`RivestSExp`, `Spki`).

## Deliberately rejected

Each is a reader error, not a misreading. The module docs list them per dialect.

- **All:** graph labels `#n=` / `#n#` (shared or cyclic data; a finite `SExp2` cannot represent
  a cycle, and no graph representation is defined here), datum comments `#;` / `#_`, read-time
  evaluation (`#.`), feature or reader conditionals (`#+`, `#-`, `#?`), reader extensions
  (`#reader`, `#lang`, tagged literals), and radix or prefixed numbers.
- **Scheme:** `#!fold-case`, `+inf.0`/`+nan.0`, complex numbers, hex escapes, `[ ]`.
- **Racket:** infix dots `(a . f . b)`, `#hash`, prefab structs, byte strings, regexps,
  backslash escapes in symbols, mixed `|…|` quoting, `#[…]`/`#{…}` vectors.
- **Common Lisp:** `#*`, `#c`, `#p`, `#a`, `#s`, potential numbers that are not supported numbers
  (CLHS 2.3.1.1, approximated conservatively), tokens of dots only.
- **Clojure:** syntax-quote (read-time namespace resolution), metadata `^`, `#(…)`, regexps,
  `##Inf`, `::kw`, namespaced maps, ratios, radix numbers, `\u` escapes.

## Remaining obligations

- Lexical layers are specified by their executable lexers; only the phrase structure has a
  declarative grammar (`Gram`). A declarative character-level grammar per dialect, and the
  relation of `DottedSExp` to the older `SExpParser.parseSExp2?`, are not yet stated.
- Floats are kept as exact decimal values (`SExpLexical.Decimal`); rounding to IEEE 754 is not
  applied. Clojure duplicate detection is structural, not Clojure value equality.
- Graph and cyclic data (Scheme/Racket/CL labels) would need a separate representation.
- The `DottedSExp.format` is stated over UTF-8 bytes through `String.fromUTF8?`; no byte-level
  roundtrip theorem yet.
- Numeric examples are checked with `cbv` rather than `decide` (rational normalization does not
  reduce in the kernel).
