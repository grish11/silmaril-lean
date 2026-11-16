module

public import Silmaril.Formats.SExp.Lexical.Defs

/-!
# Common Lisp data syntax (a documented subset of the standard reader)

Reads Common Lisp *external representations* (CLHS chapter 2, standard syntax, `*read-base*` 10,
readtable case `:upcase`) into `SExp2 CommonLisp.Atom`, using the shared phrase grammar of
`Silmaril.Formats.SExp.Reader`. Reading is purely syntactic: no read-time evaluation, no
interning, no package lookup, no feature tests.

| form | read as |
| --- | --- |
| `(a b)`, `(a . b)`, `()` | cons cells; the dot only inside a list, after an element |
| `foo`, `Foo`, `f\oo`, `|foo|`, `ab|c d|e` | `symbol` (unescaped characters upcased, ASCII only) |
| `:foo` | `keyword "FOO"` |
| `p:s`, `p::s` | `qualified "P" "S" false/true` (no package lookup) |
| `#:foo` | `uninterned "FOO"` |
| `12`, `-3/6`, `5.` | `rational` (exact, canonical: `-3/6` is `-1/2`, `5.` is `5`) |
| `1.5`, `.5`, `1e3`, `1.5d0` | `float` (exact decimal value and the exponent marker's format) |
| `"a\"b"` | `string` (`\c` is `c` for every `c`) |
| `#\a`, `#\(`, `#\Space` | `character` (names: Space, Newline, Tab, Page, Rubout, Linefeed, Return, Backspace; case-insensitive) |
| `'x`, `#'x` | the lists `(QUOTE x)`, `(FUNCTION x)` (CLHS 2.4.3, 2.4.8.2) |
| `#(a b)` | a `vector` marker head over the elements |
| `` `x ``, `,x`, `,@x` | `backquote`, `comma`, `commaAt` marker heads: CLHS 2.4.6 leaves their representation to the implementation, so they stay abstract |
| `; …`, `#| … |#` (nested) | atmosphere |

**Rejected** (the reader returns `none`): `#.` (read-time evaluation), `#+`/`#-` (feature
expressions), `#n=`/`#n#` (graph labels: finite `SExp2` has no sharing or cycles), `#*`, `#c`,
`#p`, `#a`, `#s`, `#x`/`#b`/`#o`/`#nr` (radix rationals), every other dispatch character, `,.`,
tokens of dots only (other than the consing dot), tokens that are *potential numbers*
(CLHS 2.3.1.1, approximated conservatively: the letter-adjacency refinement is not applied) but
not supported numbers, colons other than `:s`, `p:s`, `p::s`, and unescaped Backspace/Rubout.

Datum-level, not object-level: `()` reads as `SExp2.nil` while `nil` reads as the symbol `NIL`
(the same object in a Lisp image); floats keep their exact decimal value (no binary rounding).
Case conversion uses `Char.toUpper`, which converts ASCII letters only.

New definitions (sources: CLHS chapter 2).
-/

@[expose] public section

namespace Silmaril.Formats.CommonLisp

open SExpReader SExpLexical

/-- Floating-point formats selected by the exponent marker. -/
inductive FloatFormat where
  /-- No marker, or `e`/`E`: `*read-default-float-format*`. -/
  | default
  | short
  | single
  | double
  | long
  deriving DecidableEq, Repr

/-- Common Lisp atoms, and the marker heads of the encoding. -/
inductive Atom where
  | symbol (name : String)
  | keyword (name : String)
  | qualified (pkg name : String) (internal : Bool)
  | uninterned (name : String)
  | rational (q : ℚ)
  | float (d : Decimal) (fmt : FloatFormat)
  | string (s : String)
  | character (c : Char)
  /-- Marker: `#( … )`. -/
  | vector
  /-- Marker: `` `x ``. -/
  | backquote
  /-- Marker: `,x`. -/
  | comma
  /-- Marker: `,@x`. -/
  | commaAt
  deriving DecidableEq, Repr

abbrev Datum := SExp2 Atom

/-! ## Characters -/

def isWhite (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\x0c'

/-- Terminating macro characters and whitespace end a token. -/
def terminates (c : Char) : Bool :=
  isWhite c || c = '(' || c = ')' || c = '\'' || c = '"' || c = ';' || c = '`' || c = ','

/-- Constituents with the *invalid* trait: Backspace, Rubout. -/
def invalidChar (c : Char) : Bool := c = '\x08' || c = '\x7f'

/-! ## Atmosphere -/

mutual
  /-- Skip whitespace and comments; `none` for an unterminated block comment. -/
  def skip : List Char → Option (List Char)
    | [] => some []
    | c :: r =>
        if isWhite c then skip r
        else if c = ';' then skipLine r
        else if c = '#' then skipHash r
        else some (c :: r)

  def skipHash : List Char → Option (List Char)
    | [] => some ['#']
    | d :: r => if d = '|' then skipBlock 0 r else some ('#' :: d :: r)

  def skipLine : List Char → Option (List Char)
    | [] => some []
    | c :: r => if c = '\n' then skip r else skipLine r

  /-- Inside a block comment nested `depth + 1` deep. -/
  def skipBlock (depth : Nat) : List Char → Option (List Char)
    | [] => none
    | c :: r =>
        if c = '|' then blockBar depth r
        else if c = '#' then blockHash depth r
        else skipBlock depth r

  def blockBar (depth : Nat) : List Char → Option (List Char)
    | [] => none
    | e :: r =>
        if e = '#' then (match depth with
          | 0 => skip r
          | d + 1 => skipBlock d r)
        else if e = '|' then blockBar depth r
        else if e = '#' then blockHash depth r
        else skipBlock depth r

  def blockHash (depth : Nat) : List Char → Option (List Char)
    | [] => none
    | e :: r =>
        if e = '|' then skipBlock (depth + 1) r
        else if e = '#' then blockHash depth r
        else skipBlock depth r
end

/-! ## Tokens with escapes -/

/-- A token is read as characters marked escaped or not, plus a `bar` for each `|`. -/
inductive Piece where
  | ch (c : Char) (escaped : Bool)
  | bar
  deriving DecidableEq, Repr

def prepend (p : List Piece) (x : List Piece × List Char) : List Piece × List Char :=
  (p ++ x.1, x.2)

mutual
  /-- Read the rest of a token outside bars. -/
  def tokNormal : List Char → Option (List Piece × List Char)
    | [] => some ([], [])
    | c :: r =>
        if c = '\\' then tokEscN r
        else if c = '|' then (tokBar r).map (prepend [.bar])
        else if terminates c then some ([], c :: r)
        else (tokNormal r).map (prepend [.ch c false])

  def tokEscN : List Char → Option (List Piece × List Char)
    | [] => none
    | e :: r => (tokNormal r).map (prepend [.ch e true])

  /-- Read inside `|…|`. -/
  def tokBar : List Char → Option (List Piece × List Char)
    | [] => none
    | c :: r =>
        if c = '\\' then tokEscB r
        else if c = '|' then (tokNormal r).map (prepend [.bar])
        else (tokBar r).map (prepend [.ch c true])

  def tokEscB : List Char → Option (List Piece × List Char)
    | [] => none
    | e :: r => (tokBar r).map (prepend [.ch e true])
end

def Piece.isEscape : Piece → Bool
  | .ch _ e => e
  | .bar => true

def Piece.unescaped : Piece → Option Char
  | .ch c false => some c
  | _ => none

def Piece.isColon (p : Piece) : Bool := p == .ch ':' false

/-- Characters after case conversion: unescaped ones are upcased. -/
def Piece.folded : Piece → Option Char
  | .ch c false => some c.toUpper
  | .ch c true => some c
  | .bar => none

def name (ps : List Piece) : String := String.ofList (ps.filterMap Piece.folded)

/-- Split at unescaped colons (package markers). -/
def splitColon : List Piece → List (List Piece)
  | [] => [[]]
  | p :: r =>
      if p.isColon then [] :: splitColon r
      else
        match splitColon r with
        | s :: ss => (p :: s) :: ss
        | [] => [[p]]

/-! ## Numbers -/

def isMarker (c : Char) : Bool :=
  c = 'e' || c = 's' || c = 'f' || c = 'd' || c = 'l' ||
  c = 'E' || c = 'S' || c = 'F' || c = 'D' || c = 'L'

def fmtOf : Option Char → FloatFormat
  | some c =>
      if c = 's' || c = 'S' then .short else if c = 'f' || c = 'F' then .single
      else if c = 'd' || c = 'D' then .double else if c = 'l' || c = 'L' then .long
      else .default
  | none => .default

def FloatFormat.marker : FloatFormat → Char
  | .default => 'e'
  | .short => 's'
  | .single => 'f'
  | .double => 'd'
  | .long => 'l'

/-- `digits.` is an integer in Common Lisp. -/
def trailingDotInt? (cs : List Char) : Option Int :=
  match takeToken (fun c => c != '.') cs with
  | (init, ['.']) => int? init
  | _ => none

/-- Supported numeric tokens (decimal radix). -/
def number? (cs : List Char) : Option Atom :=
  match rational? cs with
  | some q => some (.rational q)
  | none =>
      match trailingDotInt? cs with
      | some n => some (.rational n)
      | none =>
          match readDecimal isMarker cs with
          | some (d, m) => some (.float d (fmtOf m))
          | none => none

def potChar (c : Char) : Bool :=
  c.isDigit || c = '+' || c = '-' || c = '/' || c = '.' || c = '^' || c = '_' || c.isAlpha

/-- Potential numbers (CLHS 2.3.1.1), without the letter-adjacency refinement: a superset. -/
def potNum (cs : List Char) : Bool :=
  cs.all potChar && cs.any Char.isDigit &&
  (match cs.head? with
    | some c => c.isDigit || c = '+' || c = '-' || c = '.' || c = '^' || c = '_'
    | none => false) &&
  (match cs.getLast? with
    | some c => !(c = '+' || c = '-')
    | none => false)

/-! ## Classifying a token -/

def symbolic (ps : List Piece) : Option (Token Atom Unit) :=
  match splitColon ps with
  | [s] => some (.atom (.symbol (name s)))
  | [p, s] =>
      if s = [] then none
      else if p = [] then some (.atom (.keyword (name s)))
      else some (.atom (.qualified (name p) (name s) false))
  | [p, m, s] =>
      if p ≠ [] ∧ m = [] ∧ s ≠ [] then some (.atom (.qualified (name p) (name s) true)) else none
  | _ => none

def classify (ps : List Piece) : Option (Token Atom Unit) :=
  if (ps.filterMap Piece.unescaped).any invalidChar then none
  else if ps.any Piece.isEscape then symbolic ps
  else
    let cs := ps.filterMap Piece.unescaped
    if cs.all (· = '.') then (if cs = ['.'] then some .dot else none)
    else if cs.contains ':' then symbolic ps
    else
      match number? cs with
      | some a => some (.atom a)
      | none => if potNum cs then none else symbolic ps

/-! ## Characters `#\…` -/

def charName? (cs : List Char) : Option Char :=
  let u := cs.map Char.toUpper
  if u = "SPACE".toList then some ' '
  else if u = "NEWLINE".toList || u = "LINEFEED".toList then some '\n'
  else if u = "TAB".toList then some '\t'
  else if u = "PAGE".toList then some '\x0c'
  else if u = "RUBOUT".toList then some '\x7f'
  else if u = "RETURN".toList then some '\r'
  else if u = "BACKSPACE".toList then some '\x08'
  else none

/-! ## The lexer -/

def ofToken : Option (Token Atom Unit) → List Char → Step Atom Unit (List Char)
  | some t, r => .token t r
  | none, _ => .error

/-- Tokens after `#`. -/
def hashDispatch : List Char → Step Atom Unit (List Char)
  | [] => .error
  | d :: r =>
      if d = '(' then .token (.open (some .vector) () false) r
      else if d = '\'' then .token (.prefix (.symbol "FUNCTION")) r
      else if d = '\\' then
        match r with
        | [] => .error
        | c :: r' =>
            match takeToken (fun c => !terminates c) r' with
            | ([], r'') => .token (.atom (.character c)) r''
            | (w, r'') =>
                match charName? (c :: w) with
                | some x => .token (.atom (.character x)) r''
                | none => .error
      else if d = ':' then
        match tokNormal r with
        | some (ps, r') =>
            if ps ≠ [] ∧ ((ps.filterMap Piece.unescaped).any invalidChar) = false ∧
                (splitColon ps).length = 1 then
              .token (.atom (.uninterned (name ps))) r'
            else .error
        | none => .error
      else .error

/-- The token starting with `c`, after atmosphere. -/
def dispatch (c : Char) (r : List Char) : Step Atom Unit (List Char) :=
  if c = '(' then .token (.open none () true) r
  else if c = ')' then .token (.close ()) r
  else if c = '\'' then .token (.prefix (.symbol "QUOTE")) r
  else if c = '`' then .token (.prefix .backquote) r
  else if c = ',' then
    match r with
    | d :: r' =>
        if d = '@' then .token (.prefix .commaAt) r'
        else if d = '.' then .error
        else .token (.prefix .comma) (d :: r')
    | [] => .token (.prefix .comma) []
  else if c = '"' then
    match readQuoted '"' some r with
    | some (w, r') => .token (.atom (.string (String.ofList w))) r'
    | none => .error
  else if c = '#' then hashDispatch r
  else
    match tokNormal (c :: r) with
    | some (ps, r') => ofToken (classify ps) r'
    | none => .error

def step (s : List Char) : Step Atom Unit (List Char) :=
  match skip s with
  | none => .error
  | some [] => .eof
  | some (c :: r) => dispatch c r

def lexer : Lexer Atom Unit (List Char) := ⟨step, List.length⟩

def role : Atom → Role Unit
  | .vector => .coll () false
  | .backquote | .comma | .commaAt => .prefix
  | _ => .plain

def syntaxNotation : Notation Atom Unit := ⟨role, (), true⟩

/-! ## Printing -/

/-- Characters that may appear in a name printed without bars. -/
def safeChar (c : Char) : Bool :=
  !terminates c && c != '|' && c != '\\' && c != ':' && c != '#' && !invalidChar c &&
    c.toUpper == c

/-- Names printed without bars: they read back as themselves. -/
def bareName (cs : List Char) : Bool :=
  cs ≠ [] && cs.all safeChar && !cs.all (· = '.') && (number? cs).isNone && !potNum cs

def nameText (s : String) : List Char :=
  if bareName s.toList then s.toList else '|' :: escapeQuoted '|' s.toList ++ ['|']

def atomText : Atom → List Char
  | .symbol s => nameText s
  | .keyword s => ':' :: nameText s
  | .qualified p s i => nameText p ++ (if i then [':', ':'] else [':']) ++ nameText s
  | .uninterned s => '#' :: ':' :: nameText s
  | .rational q => ratText q
  | .float d f => Decimal.text f.marker d
  | .string s => '"' :: escapeQuoted '"' s.toList ++ ['"']
  | .character c => ['#', '\\', c]
  | .vector => ['#', '(']
  | .backquote => ['`']
  | .comma => [',']
  | .commaAt => [',', '@']

def text : Token Atom Unit → List Char
  | .atom a => atomText a
  | .open none _ _ => ['(']
  | .open (some m) _ _ => atomText m
  | .close _ => [')']
  | .dot => ['.']
  | .prefix p => atomText p

/-- Read exactly one datum. -/
def parse? (s : String) : Option Datum := read lexer s.toList

/-- Read one datum from the front, returning the unread rest. -/
def parsePrefix? (s : String) : Option (Datum × String) :=
  (readPrefix lexer s.toList).map fun (e, r) => (e, String.ofList r)

/-- Read a sequence of data. -/
def parseAll? (s : String) : Option (List Datum) := readAll lexer s.toList

/-- Print a well-formed datum; `parse?` reads it back exactly (`Thms.parse?_print`). -/
def print (e : Datum) : String := String.ofList (SExpReader.print syntaxNotation text e)

end Silmaril.Formats.CommonLisp
