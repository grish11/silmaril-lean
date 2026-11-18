module

public import Silmaril.Formats.SExp.SchemeFamily.Defs

/-!
# Racket data as `SExp2`

`Racket.Datum := SExp2 Racket.Atom` is a documented subset of the data read by Racket's default
reader (Racket Reference §1.3, `read` with default parameters, not `read-syntax` and no `#lang`).
Reading never evaluates; reader extensions are not run.

| syntax | read as |
| --- | --- |
| `(a b)`, `[a b]`, `{a b}` | the same list (Racket's datum does not record the bracket shape) |
| `(a . b)` | improper pair |
| `#(a b)` | vector: `cons (atom .vector) (a b)` |
| `#&x` | box: `cons (atom .box) (x)` (marker prefix, printed back as `#&`) |
| symbols | `symbol`, case-sensitive; any token that is not a number; `|…|` without escapes |
| `#:kw`, `#:|k w|` | `keyword` |
| `#t #f #true #false` | `boolean` |
| `42`, `-7/2` | `exact` rational |
| `1.5`, `1e3`, `-0.0` | `inexact` literal (its exact decimal value as written; the flonum Racket reads is not computed) |
| `#\a`, `#\space`, `#\(` | `char` (names: nul null backspace tab newline linefeed vtab page return space rubout delete) |
| `"…"` | `string`, escapes `\a \b \t \n \v \f \r \e \" \' \\` |
| `'x` `` `x `` `,x` `,@x` | `(quote x)` `(quasiquote x)` `(unquote x)` `(unquote-splicing x)` |
| `#'x` `` #`x `` `#,x` `#,@x` | `(syntax x)` `(quasisyntax x)` `(unsyntax x)` `(unsyntax-splicing x)` |
| `;…`, `#|…|#` (nested) | comments |

Rejected (error, not misread): graph structure `#n=` / `#n#` (cyclic data cannot be a finite
`SExp2`; a separate graph representation would be needed), infix dots `(a . f . b)` (multiple
dots), `#;` datum comments, `#hash…`, `#s(…)` prefab structures, `#[…]` / `#{…}` vectors,
`#rx` / `#px` regexps, byte strings `#"…"`, `#reader`, `#lang`, `#!`, `#T`/`#F`, number prefixes
`#e #i #x #b #o #d`, extflonums, `+inf.0`-style and complex numbers, exponent markers other than
`e`, backslash escapes in symbols and mixed `|…|` quoting, octal/hex/Unicode string escapes, and
symbols or keywords containing `|` or `\` (unwritable here).

Data equality is syntactic (`1.5` and `1.50` read to different data); this module claims nothing
about runtime `equal?` or `=`. Racket's datum also forgets the bracket shape only because `read`
does; `read-syntax` would record it as a syntax property, which is not modelled.

New definitions (no source; syntax from the Racket Reference §1.3).
-/

@[expose] public section

namespace Silmaril.Formats.Racket

open SExpReader SExpLexical SchemeFamily

abbrev Atom := SchemeFamily.Atom
abbrev Datum := SExp2 Atom

/-- Racket's three bracket shapes. -/
inductive Closer where
  | paren
  | bracket
  | brace
  deriving DecidableEq, Repr

def opener (c : Char) : Option Closer :=
  if c = '(' then some .paren else if c = '[' then some .bracket
  else if c = '{' then some .brace else none

def closer (c : Char) : Option Closer :=
  if c = ')' then some .paren else if c = ']' then some .bracket
  else if c = '}' then some .brace else none

def closeChar : Closer → Char
  | .paren => ')'
  | .bracket => ']'
  | .brace => '}'

def isDelimiter (c : Char) : Bool :=
  Dialect.isWhitespace c || c = '(' || c = ')' || c = '[' || c = ']' || c = '{' || c = '}' ||
    c = '"' || c = ',' || c = '\'' || c = '`' || c = ';'

def stringEscape (c : Char) : Option Char :=
  if c = 'a' then some '\x07' else if c = 'b' then some '\x08' else if c = 't' then some '\t'
  else if c = 'n' then some '\n' else if c = 'v' then some '\x0b' else if c = 'f' then some '\x0c'
  else if c = 'r' then some '\r' else if c = 'e' then some '\x1b' else if c = '"' then some '"'
  else if c = '\'' then some '\'' else if c = '\\' then some '\\' else none

def charName (w : List Char) : Option Char :=
  if w = "nul".toList || w = "null".toList then some '\x00'
  else if w = "backspace".toList then some '\x08' else if w = "tab".toList then some '\t'
  else if w = "newline".toList || w = "linefeed".toList then some '\n'
  else if w = "vtab".toList then some '\x0b' else if w = "page".toList then some '\x0c'
  else if w = "return".toList then some '\r' else if w = "space".toList then some ' '
  else if w = "rubout".toList || w = "delete".toList then some '\x7f' else none

def dialect : Dialect Closer where
  brackets := ⟨.paren, opener, closer, closeChar⟩
  isDelimiter := isDelimiter
  strictIdentifiers := false
  keywords := true
  boxes := true
  bytevectors := false
  syntaxQuotes := true
  stringEscape := stringEscape
  barEscape _ := none
  charName := charName
  writableName w := !w.contains '|' && !w.contains '\\'

abbrev lexer := dialect.lexer
abbrev syntaxNotation := dialect.syntaxNotation
abbrev text := dialect.text

def parse? (s : String) : Option Datum := read lexer s.toList

def parsePrefix? (s : String) : Option (Datum × String) :=
  (readPrefix lexer s.toList).map fun (e, r) => (e, String.ofList r)

def parseAll? (s : String) : Option (List Datum) := readAll lexer s.toList

def print (e : Datum) : String := String.ofList (SExpReader.print syntaxNotation text e)

end Silmaril.Formats.Racket
