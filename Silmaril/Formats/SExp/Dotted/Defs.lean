module

public import Silmaril.Formats.SExp.Lexical.Defs
public import Silmaril.Formats.SExp.Parser
public import Silmaril.Formats.Category.Defs

/-!
# Dotted S-expression text

A plain-text syntax for `SExp2` (dotted, possibly improper S-expressions) with two atom kinds,
symbols and strings (`SExpParser.Lexeme`), so that `a` and `"a"` stay distinct. It is the common
core of the Lisp readers (R7RS §7.1.2, CLHS §2.4.1) without numbers, characters,
abbreviations or reader dispatch: every token is a symbol or a string.

## Grammar

Lexical (maximal munch, `takeToken`):

```
atmosphere ::= (whitespace | ';' <any but newline>* (newline | end))*
whitespace ::= ' ' | TAB | LF | CR | FF
delimiter  ::= whitespace | '(' | ')' | '"' | ';' | '|'
token      ::= '(' | ')' | string | quoted-symbol | dot | bare-symbol
string        ::= '"' (char-but-'"'-or-'\' | escape)* '"'
quoted-symbol ::= '|' (char-but-'|'-or-'\' | escape)* '|'
escape     ::= '\' ('\' | '"' | '|' | 'n' | 't' | 'r')
bare-symbol::= (char-but-delimiter)+ , other than the single character '.'
dot        ::= '.'   (a bare token consisting of a single '.')
```

Phrase structure (`SExpReader.Gram`, shared with the dialect readers):

```
datum ::= atom | '(' ')' | '(' datum+ ')' | '(' datum+ '.' datum ')'
```

So `(a . b)` is improper, `(a . (b))` is `(a b)`, and the following are rejected: a lone `.`
outside a list or as a datum, `( . a)` (dot first), `(a . )` (missing tail), `(a . b c)` and
`(a . b . c)` (misplaced or multiple dots), unbalanced brackets, unterminated strings, unknown
escapes. `.a`, `a.b` and `...` are ordinary symbols. Any `Lexeme` can be written: a symbol that is
empty, `.`, or contains a delimiter is printed as `|…|`.

`parse?` reads exactly one datum (only atmosphere may follow); `parsePrefix?` reads one datum
from the front and returns the rest; `parseAll?` reads a document of data. `print` writes any
datum so that `parse?` reads it back exactly (`Thms.parse?_print`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats.DottedSExp

open SExpReader SExpLexical

/-- Atoms of the dotted text syntax: symbols and strings. -/
abbrev Atom := SExpParser.Lexeme

/-- Data of the dotted text syntax. -/
abbrev Datum := SExp2 Atom

def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\x0c'

def isDelimiter (c : Char) : Bool :=
  isSpace c || c = '(' || c = ')' || c = '"' || c = ';' || c = '|'

/-- Escapes in strings and quoted symbols. -/
def escape (c : Char) : Option Char :=
  if c = '\\' then some '\\' else if c = '"' then some '"' else if c = '|' then some '|'
  else if c = 'n' then some '\n' else if c = 't' then some '\t' else if c = 'r' then some '\r'
  else none

/-- Skip atmosphere; `comment` is true inside a `;` comment. -/
def skip : Bool → List Char → List Char
  | _, [] => []
  | true, c :: r => if c = '\n' then skip false r else skip true r
  | false, c :: r =>
      if isSpace c then skip false r else if c = ';' then skip true r else c :: r

/-- One token. -/
def step (s : List Char) : Step Atom Unit (List Char) :=
  match skip false s with
  | [] => .eof
  | c :: r =>
      if c = '(' then .token (.open none () true) r
      else if c = ')' then .token (.close ()) r
      else if c = '"' then
        match readQuoted '"' escape r with
        | some (w, r') => .token (.atom (.string (String.ofList w))) r'
        | none => .error
      else if c = '|' then
        match readQuoted '|' escape r with
        | some (w, r') => .token (.atom (.symbol (String.ofList w))) r'
        | none => .error
      else
        match takeToken (fun c => !isDelimiter c) (c :: r) with
        | (w, r') => if w = ['.'] then .token .dot r' else .token (.atom (.symbol (String.ofList w))) r'

def lexer : Lexer Atom Unit (List Char) := ⟨step, List.length⟩

/-- Every atom is plain; lists admit the dot. -/
def syntaxNotation : Notation Atom Unit := ⟨fun _ => .plain, (), true⟩

/-- Symbols that can be written without bars. -/
def bare (cs : List Char) : Bool :=
  cs ≠ [] && cs.all (fun c => !isDelimiter c) && cs ≠ ['.']

def atomText : Atom → List Char
  | .string s => '"' :: escapeQuoted '"' s.toList ++ ['"']
  | .symbol s => if bare s.toList then s.toList else '|' :: escapeQuoted '|' s.toList ++ ['|']

def text : Token Atom Unit → List Char
  | .atom a => atomText a
  | .open .. => ['(']
  | .close _ => [')']
  | .dot => ['.']
  | .prefix _ => ['\'']

/-- Read exactly one datum. -/
def parse? (s : String) : Option Datum := read lexer s.toList

/-- Read one datum from the front, returning the unread rest. -/
def parsePrefix? (s : String) : Option (Datum × String) :=
  (readPrefix lexer s.toList).map fun (e, r) => (e, String.ofList r)

/-- Read a document: data separated by atmosphere. -/
def parseAll? (s : String) : Option (List Datum) := readAll lexer s.toList

/-- Print a datum; `parse?` reads it back exactly. -/
def print (e : Datum) : String := String.ofList (SExpReader.print syntaxNotation text e)

/-- The dotted text syntax as a format over UTF-8 bytes. -/
def format : Format := Format.ofDecoder fun b => (String.fromUTF8? b.data).bind parse?

end Silmaril.Formats.DottedSExp
