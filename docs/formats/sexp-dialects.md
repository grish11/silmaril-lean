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
| Collections (markers) | – | `#(…)`, `#u8(…)` (elements 0–255, `Valid`) | `#(…)`, box `#&` | `#(…)` | `[…]`, `{…}` (even; keys pairwise unequal under Clojure `Util.equiv`), `#{…}` (likewise) | – |
| Abbreviations | – | `'` `` ` `` `,` `,@` → lists | + `#'` `` #` `` `#,` `#,@` | `'` `#'` → lists; `` ` `` `,` `,@` → markers (CLHS 2.4.6) | `'` `@` `#'` `~` `~@` → lists | – |
| Symbol escapes | `\|…\|` | `\|…\|` | `\|…\|` (no escapes inside) | `\`, `\|…\|`, mixed | none (unwritable names) | none |
| Comments | `;` | `;`, nested `#\|…\|#` | `;`, nested `#\|…\|#` | `;`, nested `#\|…\|#` | `;`, commas are whitespace | `;` |
| Roundtrip | `parse?_print` (all data) | `parse?_print` (`wf`, `Valid`) | `parse?_print` (`wf`) | `parse?_print` (`wf`) | `parse?_print` (`wf`, `valid`) | `print?_sound` |
| Grammar | `parse?_iff_tokenizes` (declarative lexical + phrase grammar) | `parse?_iff` (lexer + `Gram`) | `parse?_iff` (lexer + `Gram`) | `parse?_iff` (lexer + `Gram`) | `parse?_iff` (lexer + `Gram`) | via `Pose.parse?` |
| Bytes | `format`, `decode_encode`, `isUtf8_of_decode` | – | – | – | – | – |
| Examples | `Dotted/Examples` | `Scheme/Examples` | `Racket/Examples` | `CommonLisp/Examples` | `Clojure/Examples` | `Pose2/Examples` |

"Portable S-expressions" is POSE, the `s-expressions/pose` grammar already implemented by
`Silmaril.Formats.Pose` (`SExp/Pose.lean`); it is not Rivest's canonical S-expressions
(`RivestSExp`, `Spki`).

## Numbers are syntax-level literals

Numeric atoms record what the text says, not a runtime value. Exact rationals (`ℚ`) are read
canonically where the language's reader does so (CL `-3/6` is `-1/2`, CLHS 12.1.3.2; Scheme and
Racket exact rationals). Floating literals keep the exact decimal they spell
(`SExpLexical.Decimal`: `1.5`, `1.50` and `15e-1` are three different data with one
`Decimal.value`), with no IEEE 754 rounding. Hence equality of read data is **syntactic**: none
of the Scheme, Racket or Common Lisp modules claims anything about runtime `eqv?`, `equal?`, `eql`
or `=`. The one place runtime numeric equality matters for *reading* is Clojure's duplicate-key
check, and there it is computed exactly: doubles are rounded to binary64 (nearest-even, the
repository's proved `Numeric.Ieee754.RationalRounding`) and compared with Java `==`.

## Clojure key equality

Clojure 1.12 rejects map literals with equal keys (`PersistentArrayMap.createWithCheck`,
`Util.equiv`) and set literals with equal elements (`PersistentHashSet.createWithCheck`, hash
then `Util.equiv`). `Clojure.equal?` decides `Util.equiv` on read values (`Clojure.Equal`,
`equal?_sound`):

| values | equal when |
| --- | --- |
| long, BigInt | same integer (`1` = `1N`) |
| double | same binary64 value under `==` (`0.0` = `-0.0`; `0.1` = `0.10000000000000000001`) |
| BigDecimal | same value (`compareTo`: `1.0M` = `1.00M`) |
| different numeric categories | never (`1` ≠ `1.0` ≠ `1.0M`) |
| nil, booleans, strings, characters, symbols, keywords | same atom |
| lists and vectors | element-wise (`[1 2]` = `(1 2)`, `()` = `[]`) |
| maps, sets | same size and every entry (element) of one equals one of the other, recursively and order-independently (`{:a 1 :b 2}` = `{:b 2 :a 1}`, `#{#{1 2}}` keys compare as sets); a map never equals a set or a sequence |

`Equal` is an inductive specification of this table (recursive through lists, vectors, maps and
sets); `equal?` decides it with fuel `size a + size b + 1` and is sound wherever it answers
(`equal?_sound`). The fuel always suffices when every map involved has an even number of forms
(`equal?_isSome`: each recursive call compares elements of the first value, strictly smaller
than it), and the keys a literal check compares always satisfy this, because inner literals are
checked first; so no text is ever rejected as `unsupported` (`parseError?_ne_unsupported`).
`parseE?` reports `oddMap`, `duplicate` or `syntax`, inner literals first; `Issue.unsupported`
remains in the type as a defensive case, proved unreachable from text. Accepted literals have
pairwise unequal keys (`map_literal_ok`, `set_literal_ok`), and a reported duplicate is a real
equal pair (`keysIssue_duplicate`). The map equality is Clojure's for literals with distinct
keys, which `parse?` establishes for inner literals before comparing outer keys.

`(a . b)` in Clojure: `LispReader.symbolPat` reads `.` as a symbol, so the text is the
three-element list `a . b`. The reference reserves `.`-symbols for host interop (the `.` special
form); that is evaluation, outside these modules.

## The older `SExpParser` and `SExpPrinter`

`DottedSExp` is a separate, stricter text syntax; it does not replace the older parser. The two
are related by proved statements:

- `DottedSExp.print (v.map .string) = SExpPrinter.printSExp2 v` for every `v` (same layout,
  same `\\ \" \n \r \t` escapes), so `DottedSExp.parse?` reads everything the older printer
  writes (`parse?_printSExp2`);
- on every text the older *checked* printer emits, `SExpParser.parseSExp2?` and
  `DottedSExp.parse?` agree up to the symbol/string distinction (`agrees_on_printSExp2?`).

Elsewhere they differ, deliberately, as the kernel-checked examples in `Dotted/Examples` show:
the older parser reads a lone `.` as a symbol, does not end bare tokens at `"` or `|`, decodes any
`\c` as `c`, and treats form feed as a symbol character; the dotted syntax rejects the first and
third, and delimits on `"`, `|` and form feed.

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

- **Declarative lexical grammars** exist for the dotted syntax only (`Tokenizes`, proved
  equivalent to its lexer). The Scheme, Racket, Common Lisp and Clojure lexers are their own
  lexical specification; their phrase structure is the declarative `Gram`, and their printed
  tokens are proved to lex back (`PrintLaws`).
- **Runtime numbers** (all but Clojure keys): no IEEE rounding, no `eqv?`/`eql`/`=` model.
- **Graph and cyclic data** (Scheme/Racket/CL labels) would need a separate representation.
- **Bytes**: only the dotted syntax has a byte-level `Format`; the dialects read `String`s.
- Numeric examples for Scheme and Common Lisp are checked with `cbv` (rational normalization
  does not reduce under `decide`).
