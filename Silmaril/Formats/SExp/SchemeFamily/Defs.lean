module

public import Silmaril.Formats.SExp.Lexical.Defs

/-!
# The Scheme family reader (R7RS Scheme and Racket)

One lexer, parameterized by a `Dialect`, reads the datum syntax shared by R7RS-small Scheme
(§2, §7.1.1–7.1.2) and Racket (Reference §1.3) into `SExp2 Atom`, through the shared reader
`SExpReader`. The instances are `Silmaril.Formats.Scheme` and `Silmaril.Formats.Racket`; their
module docs give the coverage tables. This module only reads text into data: no evaluation, no
read-time effects, no reader extensions.

The atom type is shared (`Atom`); atoms a dialect lacks (keywords and boxes in Scheme,
bytevectors in Racket) have role `unwritable` there, so no datum containing them is `wf`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Formats.SchemeFamily

open SExpReader SExpLexical

/-- Atoms of the Scheme family. -/
inductive Atom where
  | symbol (name : String)
  /-- Racket keyword `#:name`. -/
  | keyword (name : String)
  | boolean (value : Bool)
  /-- Exact rational (integers included): `42`, `-7/2`. -/
  | exact (value : ℚ)
  /-- Inexact decimal literal (`1.5`, `1e3`), as the exact decimal it denotes; no rounding. -/
  | inexact (value : Decimal)
  | char (value : Char)
  | string (value : String)
  /-- Marker: vector `#(…)`. -/
  | vector
  /-- Marker: R7RS bytevector `#u8(…)`. -/
  | bytevector
  /-- Marker: Racket box `#&x`. -/
  | box
  deriving DecidableEq, Repr

/-- Bracket delimiters of a dialect, indexed by its closer type `C`. -/
structure Brackets (C : Type) where
  paren : C
  opener : Char → Option C
  closer : Char → Option C
  closeChar : C → Char

/-- A Scheme-family dialect. -/
structure Dialect (C : Type) where
  brackets : Brackets C
  isDelimiter : Char → Bool
  /-- R7RS identifier grammar (`true`) or Racket's "anything that is not a number" (`false`). -/
  strictIdentifiers : Bool
  keywords : Bool
  boxes : Bool
  bytevectors : Bool
  /-- Racket's `#'`, `` #` ``, `#,`, `#,@` abbreviations. -/
  syntaxQuotes : Bool
  /-- Single-character string escapes `\c`. -/
  stringEscape : Char → Option Char
  /-- Escapes inside `|…|` symbols. -/
  barEscape : Char → Option Char
  /-- Named characters `#\name` (lowercase names). -/
  charName : List Char → Option Char
  /-- Symbol and keyword names this dialect can write (Racket cannot escape `|` or `\` inside
  bars, and this reader does not mix escapes). -/
  writableName : List Char → Bool

namespace Dialect
variable {C : Type} (D : Dialect C)

def isWhitespace (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\x0c'

/-- Characters of a bare token. -/
def bareChar (c : Char) : Bool := !D.isDelimiter c && c != '|' && c != '\\'

/-! ## Atmosphere -/

/-- Comment-skipping states: code, a `;` line comment, a `#|…|#` block comment of the given
nesting depth, and the states just after `#` (code, block) or `|` (block). -/
inductive Skip where
  | code
  | codeHash
  | line
  | block (depth : Nat)
  | blockBar (depth : Nat)
  | blockHash (depth : Nat)

/-- Skip whitespace and comments; `none` for an unterminated block comment. -/
def skip : Skip → List Char → Option (List Char)
  | .code, [] => some []
  | .code, c :: r =>
      if isWhitespace c then skip .code r
      else if c = ';' then skip .line r
      else if c = '#' then skip .codeHash r
      else some (c :: r)
  | .codeHash, [] => some ['#']
  | .codeHash, c :: r => if c = '|' then skip (.block 0) r else some ('#' :: c :: r)
  | .line, [] => some []
  | .line, c :: r => if c = '\n' then skip .code r else skip .line r
  | .block _, [] => none
  | .block n, c :: r =>
      if c = '|' then skip (.blockBar n) r
      else if c = '#' then skip (.blockHash n) r
      else skip (.block n) r
  | .blockBar _, [] => none
  | .blockBar n, c :: r =>
      if c = '#' then (if n = 0 then skip .code r else skip (.block (n - 1)) r)
      else if c = '|' then skip (.blockBar n) r
      else skip (.block n) r
  | .blockHash _, [] => none
  | .blockHash n, c :: r =>
      if c = '|' then skip (.block (n + 1)) r
      else if c = '#' then skip (.blockHash n) r
      else skip (.block n) r

/-! ## Numbers and identifiers -/

def lower (c : Char) : Char := c.toLower

/-- Tokens R7RS (§7.1.1) and Racket read as numbers, including forms this reader does not
support (which are then rejected rather than read as symbols). -/
def numericLooking (w : List Char) : Bool :=
  let l := w.map lower
  match w with
  | c :: d :: r =>
      c.isDigit || ((c = '+' || c = '-' || c = '.') && d.isDigit) ||
      ((c = '+' || c = '-') && d = '.' && (r.head?.map Char.isDigit == some true)) ||
      l.take 5 == "+inf.".toList || l.take 5 == "-inf.".toList ||
      l.take 5 == "+nan.".toList || l.take 5 == "-nan.".toList ||
      l == "+i".toList || l == "-i".toList
  | [c] => c.isDigit
  | [] => false

def isInitial (c : Char) : Bool :=
  c.isAlpha || "!$%&*/:<=>?^_~".toList.contains c || 128 ≤ c.toNat

def isSubsequent (c : Char) : Bool :=
  isInitial c || c.isDigit || c = '+' || c = '-' || c = '.' || c = '@'

def signSubsequent (c : Char) : Bool := isInitial c || c = '+' || c = '-' || c = '@'

def dotSubsequent (c : Char) : Bool := signSubsequent c || c = '.'

/-- The R7RS identifier grammar (§7.1.1) for unquoted identifiers. -/
def identifier : List Char → Bool
  | [] => false
  | c :: r =>
      if isInitial c then r.all isSubsequent
      else if c = '+' || c = '-' then
        match r with
        | [] => true
        | d :: r' =>
            (signSubsequent d && r'.all isSubsequent) ||
            (d = '.' && match r' with
              | e :: r'' => dotSubsequent e && r''.all isSubsequent
              | [] => false)
      else if c = '.' then
        match r with
        | d :: r' => dotSubsequent d && r'.all isSubsequent
        | [] => false
      else false

def isExponent (c : Char) : Bool := c = 'e' || c = 'E'

/-- Classify a bare token (not `.`). -/
def classify (w : List Char) : Option Atom :=
  if numericLooking w then
    match rational? w with
    | some q => some (.exact q)
    | none =>
        match readDecimal isExponent w with
        | some (d, _) => some (.inexact d)
        | none => none
  else if !D.strictIdentifiers || identifier w then some (.symbol (String.ofList w))
  else none

/-! ## Tokens -/

/-- A bare token: the dot, a number or a symbol. Racket mixed escapes (`a\ b`, `a|b|`) and the
like are rejected. -/
def bare (cs : List Char) : Step Atom C (List Char) :=
  match takeToken D.bareChar cs with
  | (w, r) =>
      if w = [] then .error
      else if r.head? = some '|' || r.head? = some '\\' then .error
      else if w = ['.'] then .token .dot r
      else
        match D.classify w with
        | some a => .token (.atom a) r
        | none => .error

/-- `#\`: one character, or a character name. -/
def hashChar : List Char → Step Atom C (List Char)
  | [] => .error
  | ch :: r =>
      match takeToken D.bareChar r with
      | (w, r') =>
          if w = [] then .token (.atom (.char ch)) r'
          else
            match D.charName ((ch :: w).map lower) with
            | some x => .token (.atom (.char x)) r'
            | none => .error

/-- `#u`: the bytevector opener `#u8(`. -/
def hashU8 : List Char → Step Atom C (List Char)
  | d :: e :: r => if d = '8' && e = '(' then .token (.open (some .bytevector) D.brackets.paren false) r
      else .error
  | _ => .error

/-- A keyword name without bars. -/
def keywordWord (cs : List Char) : Step Atom C (List Char) :=
  match takeToken D.bareChar cs with
  | (w, r) =>
      if w = [] || r.head? = some '|' || r.head? = some '\\' then .error
      else .token (.atom (.keyword (String.ofList w))) r

/-- `#:`: a keyword. -/
def hashKeyword : List Char → Step Atom C (List Char)
  | [] => .error
  | d :: r =>
      if d = '|' then
        match readQuoted '|' D.barEscape r with
        | some (w, r') => .token (.atom (.keyword (String.ofList w))) r'
        | none => .error
      else D.keywordWord (d :: r)

/-- `#t`, `#true`, `#f`, `#false`. -/
def hashWord (cs : List Char) : Step Atom C (List Char) :=
  match takeToken D.bareChar cs with
  | (w, r) =>
      if w = ['t'] || w = "true".toList then .token (.atom (.boolean true)) r
      else if w = ['f'] || w = "false".toList then .token (.atom (.boolean false)) r
      else .error

/-- A comma abbreviation, `,x` or `,@x` (and Racket's `#,x`, `#,@x`). -/
def comma (plain splicing : String) : List Char → Step Atom C (List Char)
  | [] => .token (.prefix (.symbol plain)) []
  | d :: r =>
      if d = '@' then .token (.prefix (.symbol splicing)) r
      else .token (.prefix (.symbol plain)) (d :: r)

/-- After `#`. -/
def hash : List Char → Step Atom C (List Char)
  | [] => .error
  | c :: r =>
      if c = '(' then .token (.open (some .vector) D.brackets.paren false) r
      else if c = '\\' then D.hashChar r
      else if c = 'u' && D.bytevectors then D.hashU8 r
      else if c = ':' && D.keywords then D.hashKeyword r
      else if c = '&' && D.boxes then .token (.prefix .box) r
      else if c = '\'' && D.syntaxQuotes then .token (.prefix (.symbol "syntax")) r
      else if c = '`' && D.syntaxQuotes then .token (.prefix (.symbol "quasisyntax")) r
      else if c = ',' && D.syntaxQuotes then comma "unsyntax" "unsyntax-splicing" r
      else D.hashWord (c :: r)

/-- One token after atmosphere. -/
def dispatch (c : Char) (r : List Char) : Step Atom C (List Char) :=
  match D.brackets.opener c with
  | some k => .token (.open none k true) r
  | none =>
      match D.brackets.closer c with
      | some k => .token (.close k) r
      | none =>
          if c = '"' then
            match readQuoted '"' D.stringEscape r with
            | some (w, r') => .token (.atom (.string (String.ofList w))) r'
            | none => .error
          else if c = '|' then
            match readQuoted '|' D.barEscape r with
            | some (w, r') => .token (.atom (.symbol (String.ofList w))) r'
            | none => .error
          else if c = '\'' then .token (.prefix (.symbol "quote")) r
          else if c = '`' then .token (.prefix (.symbol "quasiquote")) r
          else if c = ',' then comma "unquote" "unquote-splicing" r
          else if c = '#' then D.hash r
          else D.bare (c :: r)

def step (s : List Char) : Step Atom C (List Char) :=
  match skip .code s with
  | none => .error
  | some [] => .eof
  | some (c :: r) => D.dispatch c r

def lexer : Lexer Atom C (List Char) := ⟨D.step, List.length⟩

/-! ## Encoding and printing -/

def role : Atom → Role C
  | .symbol s => if D.writableName s.toList then .plain else .unwritable
  | .keyword s => if D.keywords && D.writableName s.toList then .plain else .unwritable
  | .vector => .coll D.brackets.paren false
  | .bytevector => if D.bytevectors then .coll D.brackets.paren false else .unwritable
  | .box => if D.boxes then .prefix else .unwritable
  | _ => .plain

def syntaxNotation : Notation Atom C := ⟨D.role, D.brackets.paren, true⟩

/-- A symbol name that can be written without bars. -/
def bareSymbol (w : List Char) : Bool :=
  match w with
  | [] => false
  | c :: _ =>
      w.all D.bareChar && c != '\'' && c != '`' && c != ',' && c != '#' && w != ['.'] &&
        D.classify w == some (.symbol (String.ofList w))

def atomText : Atom → List Char
  | .symbol s => if D.bareSymbol s.toList then s.toList else '|' :: escapeQuoted '|' s.toList ++ ['|']
  | .keyword s =>
      if s.toList ≠ [] ∧ s.toList.all D.bareChar then '#' :: ':' :: s.toList
      else '#' :: ':' :: '|' :: escapeQuoted '|' s.toList ++ ['|']
  | .boolean b => if b then ['#', 't'] else ['#', 'f']
  | .exact q => ratText q
  | .inexact d => Decimal.text 'e' d
  | .char c => ['#', '\\', c]
  | .string s => '"' :: escapeQuoted '"' s.toList ++ ['"']
  | .vector => ['#', '(']
  | .bytevector => ['#', 'u', '8', '(']
  | .box => ['#', '&']

def text : Token Atom C → List Char
  | .atom a => D.atomText a
  | .open (some m) _ _ => D.atomText m
  | .open none _ _ => ['(']
  | .close k => [D.brackets.closeChar k]
  | .dot => ['.']
  | .prefix p => D.atomText p

/-- Facts about a dialect's character classes that the generic roundtrip proof uses. Each
instance proves them by computation. -/
structure Laws : Prop where
  opener_paren : D.brackets.opener '(' = some D.brackets.paren
  delim_opener : ∀ c k, D.brackets.opener c = some k → D.isDelimiter c = true
  delim_closer : ∀ c k, D.brackets.closer c = some k → D.isDelimiter c = true
  closer_closeChar : ∀ k, D.brackets.closer (D.brackets.closeChar k) = some k
  opener_closeChar : ∀ k, D.brackets.opener (D.brackets.closeChar k) = none
  delim_closeChar : ∀ k, D.isDelimiter (D.brackets.closeChar k) = true
  closeChar_special : ∀ k, D.brackets.closeChar k ≠ '|' ∧ D.brackets.closeChar k ≠ '\\' ∧
    D.brackets.closeChar k ≠ ';' ∧ D.brackets.closeChar k ≠ '#' ∧
    isWhitespace (D.brackets.closeChar k) = false
  opener_special : D.brackets.opener '"' = none ∧ D.brackets.opener '|' = none ∧
    D.brackets.opener '#' = none
  closer_special : D.brackets.closer '"' = none ∧ D.brackets.closer '|' = none ∧
    D.brackets.closer '#' = none
  delim_space : ∀ c, isWhitespace c = true → D.isDelimiter c = true
  delim_special : D.isDelimiter ';' = true ∧ D.isDelimiter '"' = true
  /-- Characters of numerals and `#` words are not delimiters. -/
  notDelim : ∀ c, (c.isDigit = true ∨ c = '-' ∨ c = 'e' ∨ c = '/' ∨ c = '.' ∨ c = 't' ∨
    c = 'f') → D.isDelimiter c = false
  string_backslash : D.stringEscape '\\' = some '\\'
  string_quote : D.stringEscape '"' = some '"'
  bar : ∀ w rest, D.writableName w = true →
    readQuoted '|' D.barEscape (escapeQuoted '|' w ++ '|' :: rest) = some (w, rest)
  /-- Names read between bars are writable. -/
  bar_writable : ∀ cs w rest, readQuoted '|' D.barEscape cs = some (w, rest) →
    D.writableName w = true
  /-- Names read bare are writable. -/
  bare_writable : ∀ w, w.all D.bareChar = true → D.writableName w = true
  /-- The abbreviation heads are writable. -/
  quote_writable : ∀ s ∈ ["quote", "quasiquote", "unquote", "unquote-splicing", "syntax",
    "quasisyntax", "unsyntax", "unsyntax-splicing"], D.writableName s.toList = true

end Dialect

end Silmaril.Formats.SchemeFamily
