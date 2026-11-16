module

public import Silmaril.Formats.SExp.Lexical.Defs

/-!
# Clojure data syntax (a documented subset of the Clojure reader)

Reads the data syntax of the Clojure reader (<https://clojure.org/reference/reader>) into
`SExp2 Clojure.Atom` through the shared reader (`SExpReader`). Reading is purely syntactic: no
evaluation, no namespace resolution, no reader functions.

## Encoding

Clojure has **no dotted pairs**: `listDotted = false` and the lexer never emits a dot token, so
`.` is an ordinary symbol and `(a . b)` is a three-element list. A list `(…)` is a nil-terminated
`SExp2` spine; the empty list `()` is `SExp2.nil`, distinct from the literal `nil`
(`Atom.nil`). Vectors, maps and sets keep their syntax-level identity through **marker atoms**
(`SExpReader` encoding): `[a b]` ↦ `cons (atom vector) (a b)`, `{k v}` ↦ `cons (atom map) (k v)`,
`#{a}` ↦ `cons (atom set) (a)`. Markers are never read as atoms, so the four collection kinds of
`(a b)`, `[a b]`, `{a b}`, `#{a b}` give four distinct data (`Examples`). `Valid` additionally
requires an even number of forms in a map, no duplicate map keys and no duplicate set elements;
duplicates are detected by structural equality of the read data, whereas Clojure uses value
equality (`1` and `1N` are equal keys in Clojure, distinct here).

## Coverage

| form | support |
| --- | --- |
| lists `( )`, vectors `[ ]`, maps `{ }`, sets `#{ }` | read; markers for vector/map/set |
| `nil`, `true`, `false` | literal atoms (`nil` is not the empty list) |
| integers `42`, `-7`, `+3`, `42N` | `integer n big`: `big` for the `N` suffix or outside the 64-bit range |
| floats `1.5`, `1e3`, `-2.5e-3`, `1.5M`, `1M` | `float d bigDecimal`: exact decimal (`SExpLexical.Decimal`), no binary rounding |
| strings `"…"` with escapes `\t \b \n \r \f \' \" \\` | `string` |
| characters `\c`, `\newline \space \tab \backspace \formfeed \return` | `char` |
| symbols `foo`, `ns/foo`, `/`, `ns//`, `.`, `a.b` | `symbol ns name`, ASCII name grammar `validSegment` |
| keywords `:foo`, `:ns/foo` | `keyword ns name` |
| `'x` `@x` `#'x` `~x` `~@x` | read as `(quote x)`, `(clojure.core/deref x)`, `(var x)`, `(clojure.core/unquote x)`, `(clojure.core/unquote-splicing x)` |
| `;` comments, commas | atmosphere |
| `` `x `` syntax-quote | **rejected**: namespace resolution and gensyms happen at read time |
| `^meta` | **rejected** (metadata attaches to the next form) |
| `#(…)` `#_` `#"…"` `#inst` `#uuid` `#tag` `#?` `#?@` `##Inf` `##NaN` `#:ns{…}` `#!` | **rejected** |
| `::kw` auto-resolved keywords | **rejected** (needs the current namespace) |
| radix `2r101`, hex `0x1F`, octal `017`, ratios `1/2`, leading zeros | **rejected** |
| string escapes `\uXXXX`, `\ooo`; characters `\uXXXX`, `\oNNN` | **rejected** |
| non-ASCII letters in symbols and keywords | **rejected** (outside `validSegment`) |

Symbols and keywords cannot be escaped in Clojure, so an atom whose name falls outside the
grammar has role `unwritable`: no datum containing it is `wf`, and the reader never produces it.
Likewise `integer n false` outside the 64-bit range (the reader marks it `big`).

New definitions (no source beyond the Clojure reader reference).
-/

@[expose] public section

namespace Silmaril.Formats.Clojure

open SExpReader SExpLexical

/-- The closing delimiters `)`, `]`, `}`. -/
inductive Closer where
  | paren
  | bracket
  | brace
  deriving DecidableEq, Repr

/-- Clojure atoms, plus the three collection markers. -/
inductive Atom where
  | nil
  | boolean (b : Bool)
  /-- An integer; `big` is a `clojure.lang.BigInt` (`N` suffix), otherwise a `long`. -/
  | integer (n : Int) (big : Bool)
  /-- A floating literal's exact decimal value; `bigDecimal` for the `M` suffix. -/
  | float (d : Decimal) (bigDecimal : Bool)
  | string (s : String)
  | char (c : Char)
  | symbol (ns : Option String) (name : String)
  | keyword (ns : Option String) (name : String)
  /-- Marker of `[…]`. -/
  | vector
  /-- Marker of `{…}`. -/
  | map
  /-- Marker of `#{…}`. -/
  | set
  deriving DecidableEq, Repr

/-- Clojure data. -/
abbrev Datum := SExp2 Atom

/-! ## Characters and names -/

/-- Whitespace; commas are whitespace in Clojure. -/
def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = ',' || c = '\x0c'

/-- Characters that end a token: whitespace and the terminating macro characters. -/
def isDelimiter (c : Char) : Bool :=
  isSpace c || c = '"' || c = ';' || c = '@' || c = '^' || c = '`' || c = '~' ||
    c = '(' || c = ')' || c = '[' || c = ']' || c = '{' || c = '}' || c = '\\'

def isSign (c : Char) : Bool := c = '+' || c = '-'

/-- Characters of symbol and keyword names (ASCII). -/
def nameChar (c : Char) : Bool :=
  c.isAlphanum || c = '*' || c = '+' || c = '!' || c = '-' || c = '_' || c = '\'' ||
    c = '?' || c = '<' || c = '>' || c = '=' || c = '.' || c = '$' || c = '&' || c = '%' ||
    c = '#'

def noDoubleColon : List Char → Bool
  | a :: b :: r => !(a = ':' && b = ':') && noDoubleColon (b :: r)
  | _ => true

/-- Whether a token starts like a number: a digit, or a sign followed by a digit. -/
def numericStart : List Char → Bool
  | [] => false
  | c :: r => c.isDigit || (isSign c && match r with
      | d :: _ => d.isDigit
      | [] => false)

/-- One namespace or name segment: nonempty, not numeric, not starting with `#`, `'` or `:`,
name characters (and inner single colons), not ending with `:`, no `/`. -/
def validSegment (cs : List Char) : Bool :=
  match cs with
  | [] => false
  | c :: r =>
      nameChar c && c != '#' && c != '\'' && !numericStart (c :: r) &&
        r.all (fun d => nameChar d || d = ':') && noDoubleColon (c :: r) &&
        (c :: r).getLast? != some ':'

/-- The symbol grammar: `/`, `name`, `ns/name` or `ns//`; `nil`, `true`, `false` are literals. -/
def symbolOK : Option String → String → Bool
  | none, n => (n.toList = ['/'] || validSegment n.toList) && n != "nil" && n != "true" &&
      n != "false"
  | some ns, n => validSegment ns.toList && (n.toList = ['/'] || validSegment n.toList)

/-- The keyword grammar (after the leading colon). -/
def keywordOK : Option String → String → Bool
  | none, n => validSegment n.toList
  | some ns, n => validSegment ns.toList && validSegment n.toList

def longRange (n : Int) : Bool := decide (-(2 ^ 63 : Int) ≤ n ∧ n < 2 ^ 63)

/-! ## Notation -/

/-- Roles: the three collection markers; symbols, keywords and longs outside their grammar have
no written form. -/
def role : Atom → Role Closer
  | .vector => .coll .bracket false
  | .map => .coll .brace false
  | .set => .coll .brace false
  | .symbol ns n => if symbolOK ns n then .plain else .unwritable
  | .keyword ns n => if keywordOK ns n then .plain else .unwritable
  | .integer n big => if big || longRange n then .plain else .unwritable
  | _ => .plain

def syntaxNotation : Notation Atom Closer := ⟨role, .paren, false⟩

/-! ## Lexer -/

/-- String escapes. -/
def escape (c : Char) : Option Char :=
  if c = '\\' then some '\\' else if c = '"' then some '"' else if c = '\'' then some '\''
  else if c = 't' then some '\t' else if c = 'b' then some '\x08'
  else if c = 'n' then some '\n' else if c = 'r' then some '\r' else if c = 'f' then some '\x0c'
  else none

/-- Named characters. -/
def charName (c : Char) : Option (List Char) :=
  if c = '\n' then some ['n', 'e', 'w', 'l', 'i', 'n', 'e']
  else if c = ' ' then some ['s', 'p', 'a', 'c', 'e']
  else if c = '\t' then some ['t', 'a', 'b']
  else if c = '\x08' then some ['b', 'a', 'c', 'k', 's', 'p', 'a', 'c', 'e']
  else if c = '\x0c' then some ['f', 'o', 'r', 'm', 'f', 'e', 'e', 'd']
  else if c = '\r' then some ['r', 'e', 't', 'u', 'r', 'n']
  else none

def charOfName (w : List Char) : Option Char :=
  if w = ['n', 'e', 'w', 'l', 'i', 'n', 'e'] then some '\n'
  else if w = ['s', 'p', 'a', 'c', 'e'] then some ' '
  else if w = ['t', 'a', 'b'] then some '\t'
  else if w = ['b', 'a', 'c', 'k', 's', 'p', 'a', 'c', 'e'] then some '\x08'
  else if w = ['f', 'o', 'r', 'm', 'f', 'e', 'e', 'd'] then some '\x0c'
  else if w = ['r', 'e', 't', 'u', 'r', 'n'] then some '\r'
  else none

/-- Split `ns/name` at the first slash. -/
def symParts (w : List Char) : Option (Option String × String) :=
  match takeToken (fun c => c != '/') w with
  | (ns, []) => some (none, String.ofList ns)
  | (ns, _ :: name) =>
      if ns = [] then (if name = [] then some (none, "/") else none)
      else some (some (String.ofList ns), String.ofList name)

/-- An integer token: optional sign, then digits without leading zeros. -/
def intToken? (w : List Char) : Option Int :=
  match int? w with
  | some n => if w = intText n || w = '+' :: intText n || (n = 0 && w = ['-', '0']) then some n
      else none
  | none => none

def isExp (c : Char) : Bool := c = 'e' || c = 'E'

def classifyNumber (w : List Char) : Option Atom :=
  if w.getLast? = some 'N' then (intToken? w.dropLast).map fun n => .integer n true
  else if w.getLast? = some 'M' then
    match readDecimal isExp w.dropLast with
    | some (d, _) => some (.float d true)
    | none => (intToken? w.dropLast).map fun n => .float ⟨decide (n < 0), n.natAbs, 0⟩ true
  else
    match intToken? w with
    | some n => some (.integer n (!longRange n))
    | none =>
        match readDecimal isExp w with
        | some (d, _) => some (.float d false)
        | none => none

/-- Classify a bare token. -/
def classify (w : List Char) : Option Atom :=
  if numericStart w then classifyNumber w
  else
    match w with
    | [] => none
    | c :: r =>
        if c = ':' then
          if r.head? = some ':' then none
          else
            match symParts r with
            | some (ns, n) => if keywordOK ns n then some (.keyword ns n) else none
            | none => none
        else
          match symParts w with
          | some (none, n) =>
              if n = "nil" then some .nil
              else if n = "true" then some (.boolean true)
              else if n = "false" then some (.boolean false)
              else if symbolOK none n then some (.symbol none n) else none
          | some (some ns, n) => if symbolOK (some ns) n then some (.symbol (some ns) n) else none
          | none => none

/-- Skip atmosphere; `comment` is true inside a `;` comment. -/
def skip : Bool → List Char → List Char
  | _, [] => []
  | true, c :: r => if c = '\n' then skip false r else skip true r
  | false, c :: r =>
      if isSpace c then skip false r else if c = ';' then skip true r else c :: r

def sym (ns : Option String) (n : String) : Atom := .symbol ns n

def bareToken (w : List Char) : Step Atom Closer (List Char) :=
  match takeToken (fun c => !isDelimiter c) w with
  | (tok, r) =>
      match classify tok with
      | some a => .token (.atom a) r
      | none => .error

def charToken : List Char → Step Atom Closer (List Char)
  | [] => .error
  | c :: r =>
      match takeToken (fun c => !isDelimiter c) r with
      | (w, r') =>
          if w = [] then .token (.atom (.char c)) r'
          else
            match charOfName (c :: w) with
            | some ch => .token (.atom (.char ch)) r'
            | none => .error

def hashToken : List Char → Step Atom Closer (List Char)
  | [] => .error
  | d :: r =>
      if d = '{' then .token (.open (some .set) .brace false) r
      else if d = '\'' then .token (.prefix (sym none "var")) r
      else .error

/-- One token, before the notation check. -/
def rawStep (s : List Char) : Step Atom Closer (List Char) :=
  match skip false s with
  | [] => .eof
  | c :: r =>
      if c = '(' then .token (.open none .paren false) r
      else if c = ')' then .token (.close .paren) r
      else if c = '[' then .token (.open (some .vector) .bracket false) r
      else if c = ']' then .token (.close .bracket) r
      else if c = '{' then .token (.open (some .map) .brace false) r
      else if c = '}' then .token (.close .brace) r
      else if c = '"' then
        match readQuoted '"' escape r with
        | some (w, r') => .token (.atom (.string (String.ofList w))) r'
        | none => .error
      else if c = '\\' then charToken r
      else if c = '\'' then .token (.prefix (sym none "quote")) r
      else if c = '@' then .token (.prefix (sym (some "clojure.core") "deref")) r
      else if c = '~' then
        match r with
        | d :: r' =>
            if d = '@' then .token (.prefix (sym (some "clojure.core") "unquote-splicing")) r'
            else .token (.prefix (sym (some "clojure.core") "unquote")) r
        | [] => .token (.prefix (sym (some "clojure.core") "unquote")) r
      else if c = '#' then hashToken r
      else if c = '`' || c = '^' then .error
      else bareToken (c :: r)

/-- Whether a token respects the notation (`Notation.TokenOK`, decided). -/
def tokenOK : Token Atom Closer → Bool
  | .atom a => (role a).isPlain
  | .open none _ d => !d
  | .open (some m) c d => role m = .coll c d
  | .prefix p => (role p).isPlain
  | .close _ => true
  | .dot => false

/-- One token: `rawStep`, rejecting tokens outside the notation. -/
def step (s : List Char) : Step Atom Closer (List Char) :=
  match rawStep s with
  | .token t r => if tokenOK t then .token t r else .error
  | x => x

def lexer : Lexer Atom Closer (List Char) := ⟨step, List.length⟩

/-! ## Printing -/

def symText : Option String → String → List Char
  | none, n => n.toList
  | some ns, n => ns.toList ++ '/' :: n.toList

def charText (c : Char) : List Char :=
  match charName c with
  | some nm => nm
  | none => [c]

def atomText : Atom → List Char
  | .nil => ['n', 'i', 'l']
  | .boolean true => ['t', 'r', 'u', 'e']
  | .boolean false => ['f', 'a', 'l', 's', 'e']
  | .integer n big => intText n ++ (if big then ['N'] else [])
  | .float d big => Decimal.text 'e' d ++ (if big then ['M'] else [])
  | .string s => '"' :: escapeQuoted '"' s.toList ++ ['"']
  | .char c => '\\' :: charText c
  | .symbol ns n => symText ns n
  | .keyword ns n => ':' :: symText ns n
  | _ => ['#', '?']

def text : Token Atom Closer → List Char
  | .atom a => if (role a).isPlain then atomText a else ['#', '?']
  | .open (some .vector) _ _ => ['[']
  | .open (some .map) _ _ => ['{']
  | .open (some .set) _ _ => ['#', '{']
  | .open _ _ _ => ['(']
  | .close .paren => [')']
  | .close .bracket => [']']
  | .close .brace => ['}']
  | .dot => ['.']
  | .prefix _ => ['\'']

/-! ## Collection validity -/

def elems : SExp2 Atom → List (SExp2 Atom)
  | .cons x r => x :: elems r
  | _ => []

/-- Keys: the elements at even positions. -/
def keysOf : List (SExp2 Atom) → List (SExp2 Atom)
  | k :: _ :: r => k :: keysOf r
  | [k] => [k]
  | [] => []

/-- Maps have an even number of forms and distinct keys; sets have distinct elements. -/
def valid : SExp2 Atom → Bool
  | .nil => true
  | .atom _ => true
  | .cons x r =>
      (match x with
        | .atom .map => (elems r).length % 2 == 0 && decide (keysOf (elems r)).Nodup
        | .atom .set => decide (elems r).Nodup
        | _ => true) && valid x && valid r

/-! ## Entry points -/

/-- Read exactly one datum. -/
def parse? (s : String) : Option Datum := (read lexer s.toList).filter valid

/-- Read one datum from the front, returning the unread rest. -/
def parsePrefix? (s : String) : Option (Datum × String) :=
  (readPrefix lexer s.toList).bind fun (e, r) =>
    if valid e then some (e, String.ofList r) else none

/-- Read a document: data separated by atmosphere. -/
def parseAll? (s : String) : Option (List Datum) :=
  (readAll lexer s.toList).filter fun es => es.all valid

/-- Print a well-formed datum. -/
def print (e : Datum) : String := String.ofList (SExpReader.print syntaxNotation text e)

end Silmaril.Formats.Clojure
