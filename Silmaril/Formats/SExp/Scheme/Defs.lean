module

public import Silmaril.Formats.SExp.SchemeFamily.Defs

/-!
# Scheme (R7RS-small) data as `SExp2`

`Scheme.Datum := SExp2 Scheme.Atom` is the external representation of data of R7RS-small
(§2.1–2.4, §6, §7.1.1–7.1.2), read by the Scheme-family lexer. Reading never evaluates.

| syntax | read as |
| --- | --- |
| `(a b)`, `(a . b)`, `()` | cons spine, improper with dotted tail, `nil` |
| `#(a b)` | vector: `cons (atom .vector) (a b)` (no dot inside) |
| `#u8(1 2)` | bytevector: `cons (atom .bytevector) (1 2)`; elements must be exact `0..255` (`Valid`) |
| identifiers | `symbol`, R7RS identifier grammar, case-sensitive; `|…|` with `\|`, `\\`, `\a \b \t \n \r` |
| `#t #f #true #false` | `boolean` |
| `42`, `-7/2` | `exact` rational (`4/2` is `2`) |
| `1.5`, `.5`, `-1e3`, `2.` | `inexact` decimal (exact decimal value, no rounding) |
| `#\a`, `#\space`, `#\(` | `char` (names: alarm backspace delete escape newline null return space tab) |
| `"…"` | `string`, escapes `\a \b \t \n \r \" \\ \|` |
| `'x` `` `x `` `,x` `,@x` | `(quote x)` `(quasiquote x)` `(unquote x)` `(unquote-splicing x)` |
| `;…`, `#|…|#` (nested) | comments |

Rejected (error, not misread): `#;` datum comments, `#!fold-case` / `#!no-fold-case` directives,
datum labels `#n=` / `#n#` (shared and cyclic structure; finite `SExp2` cannot represent cycles),
number prefixes `#e #i #x #b #o #d`, `+inf.0 -inf.0 +nan.0 -nan.0`, complex numbers, exponent
markers other than `e`, hex escapes `\x…;` in strings, symbols and characters, string line
continuations, `[ ]` and `{ }` (reserved by R7RS), and tokens that are neither numbers nor
identifiers.

New definitions (no source; syntax from R7RS-small).
-/

@[expose] public section

namespace Silmaril.Formats.Scheme

open SExpReader SExpLexical SchemeFamily

abbrev Atom := SchemeFamily.Atom
abbrev Datum := SExp2 Atom

def isDelimiter (c : Char) : Bool :=
  Dialect.isWhitespace c || c = '(' || c = ')' || c = '"' || c = ';' || c = '|'

/-- Mnemonic escapes of R7RS §6.7 (strings) and §2.1 (`|…|`), and `\\`. -/
def escape (c : Char) : Option Char :=
  if c = 'a' then some '\x07' else if c = 'b' then some '\x08' else if c = 't' then some '\t'
  else if c = 'n' then some '\n' else if c = 'r' then some '\r' else if c = '"' then some '"'
  else if c = '\\' then some '\\' else if c = '|' then some '|' else none

def charName (w : List Char) : Option Char :=
  if w = "alarm".toList then some '\x07' else if w = "backspace".toList then some '\x08'
  else if w = "delete".toList then some '\x7f' else if w = "escape".toList then some '\x1b'
  else if w = "newline".toList then some '\n' else if w = "null".toList then some '\x00'
  else if w = "return".toList then some '\r' else if w = "space".toList then some ' '
  else if w = "tab".toList then some '\t' else none

def dialect : Dialect Unit where
  brackets := ⟨(), fun c => if c = '(' then some () else none,
    fun c => if c = ')' then some () else none, fun _ => ')'⟩
  isDelimiter := isDelimiter
  strictIdentifiers := true
  keywords := false
  boxes := false
  bytevectors := true
  syntaxQuotes := false
  stringEscape := escape
  barEscape := escape
  charName := charName
  writableName _ := true

abbrev lexer := dialect.lexer
abbrev syntaxNotation := dialect.syntaxNotation
abbrev text := dialect.text

mutual
  /-- Bytevector elements are exact integers in `0..255` (R7RS §6.9). -/
  def Valid : Datum → Bool
    | .cons (.atom .bytevector) r => validBytes r
    | .cons x r => Valid x && Valid r
    | _ => true

  def validBytes : Datum → Bool
    | .nil => true
    | .cons (.atom (.exact q)) r => q.den == 1 && 0 ≤ q.num && q.num ≤ 255 && validBytes r
    | _ => false
end

/-- Read exactly one datum. -/
def parse? (s : String) : Option Datum :=
  match read lexer s.toList with
  | some e => if Valid e then some e else none
  | none => none

/-- Read one datum from the front, returning the rest. -/
def parsePrefix? (s : String) : Option (Datum × String) :=
  match readPrefix lexer s.toList with
  | some (e, r) => if Valid e then some (e, String.ofList r) else none
  | none => none

/-- Read a document: data separated by atmosphere, each valid. -/
def parseAll? (s : String) : Option (List Datum) :=
  match readAll lexer s.toList with
  | some es => if es.all (Valid ·) then some es else none
  | none => none

/-- Print a well-formed datum. -/
def print (e : Datum) : String := String.ofList (SExpReader.print syntaxNotation text e)

end Silmaril.Formats.Scheme
