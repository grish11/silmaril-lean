module

public import Init.Data.List.SplitOn.Lemmas
public import Std.Data.String.ToNat

/-! Shared lexer for Cambridge concrete syntax. Input must be valid UTF-8.
Words use ASCII characters and are read at maximal length. Keywords and locations
are separate from variables. The lexer accepts ASCII aliases for the printed
comparison, arrow and minus signs. -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concrete

inductive DataKeyword where
  | fst | snd | inl | inr | matchK | withK | ref
  deriving DecidableEq, Repr

def DataKeyword.text : DataKeyword → String
  | .fst => "fst"
  | .snd => "snd"
  | .inl => "inl"
  | .inr => "inr"
  | .matchK => "match"
  | .withK => "with"
  | .ref => "ref"

inductive Keyword where
  | trueK | falseK | skip | ifK | thenK | elseK | whileK | doK | doneK
  | funK | letK | recK | inK | int | bool | unit
  | data (keyword : DataKeyword)
  deriving DecidableEq, Repr

def Keyword.text : Keyword → String
  | .trueK => "true"
  | .falseK => "false"
  | .skip => "skip"
  | .ifK => "if"
  | .thenK => "then"
  | .elseK => "else"
  | .whileK => "while"
  | .doK => "do"
  | .doneK => "done"
  | .funK => "fun"
  | .letK => "let"
  | .recK => "rec"
  | .inK => "in"
  | .int => "int"
  | .bool => "bool"
  | .unit => "unit"
  | .data keyword => keyword.text

inductive Punct where
  | openP | closeP | add | ge | minus | deref | assign | seq | colon | equals | arrow
  | openBrace | closeBrace | comma | dot | bar | product
  deriving DecidableEq, Repr

def Punct.chars : Punct → List Char
  | .openP => ['(']
  | .closeP => [')']
  | .add => ['+']
  | .ge => ['≥']
  | .minus => ['−']
  | .deref => ['!']
  | .assign => [':', '=']
  | .seq => [';']
  | .colon => [':']
  | .equals => ['=']
  | .arrow => ['→']
  | .openBrace => ['{']
  | .closeBrace => ['}']
  | .comma => [',']
  | .dot => ['.']
  | .bar => ['|']
  | .product => ['∗']

inductive Token where
  | keyword (k : Keyword)
  | punct (p : Punct)
  | number (n : Nat)
  | location (name : String)
  | variable (name : String)
  deriving DecidableEq, Repr

def wordChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- The course location letters are `l` followed by zero or more decimal digits. -/
def locationWord : List Char → Bool
  | 'l' :: digits => digits.all Char.isDigit
  | _ => false

/-- The character shape of a variable before reserving keywords and locations. -/
def identifierWord : List Char → Bool
  | c :: cs => (c.isAlpha || c == '_') && cs.all wordChar
  | [] => false

/-- Classify a maximal word. Check decimal digits explicitly to exclude digit separators. -/
def classifyWord (cs : List Char) : Option Token :=
  let text := String.ofList cs
  if cs.all Char.isDigit then text.toNat?.map .number
  else if locationWord cs then some (.location text)
  else match text with
  | "true" => some (.keyword .trueK)
  | "false" => some (.keyword .falseK)
  | "skip" => some (.keyword .skip)
  | "if" => some (.keyword .ifK)
  | "then" => some (.keyword .thenK)
  | "else" => some (.keyword .elseK)
  | "while" => some (.keyword .whileK)
  | "do" => some (.keyword .doK)
  | "done" => some (.keyword .doneK)
  | "fun" => some (.keyword .funK)
  | "let" => some (.keyword .letK)
  | "rec" => some (.keyword .recK)
  | "in" => some (.keyword .inK)
  | "int" => some (.keyword .int)
  | "bool" => some (.keyword .bool)
  | "unit" => some (.keyword .unit)
  | _ =>
    if identifierWord cs then some (.variable text)
    else none

/-- A nonempty maximal word. -/
def IsWord (cs : List Char) : Prop := cs ≠ [] ∧ cs.all wordChar = true

instance (cs : List Char) : Decidable (IsWord cs) := inferInstanceAs (Decidable (_ ∧ _))

/-- Name restrictions for the canonical source printer. -/
def IsLocation (s : String) : Prop :=
  IsWord s.toList ∧ classifyWord s.toList = some (.location s)

def IsVariable (s : String) : Prop :=
  IsWord s.toList ∧ classifyWord s.toList = some (.variable s)

instance (s : String) : Decidable (IsLocation s) := inferInstanceAs (Decidable (_ ∧ _))
instance (s : String) : Decidable (IsVariable s) := inferInstanceAs (Decidable (_ ∧ _))

def readPunct : List Char → Option (Punct × List Char)
  | ':' :: '=' :: rest => some (.assign, rest)
  | '>' :: '=' :: rest => some (.ge, rest)
  | '-' :: '>' :: rest => some (.arrow, rest)
  | '(' :: rest => some (.openP, rest)
  | ')' :: rest => some (.closeP, rest)
  | '+' :: rest => some (.add, rest)
  | '≥' :: rest => some (.ge, rest)
  | '-' :: rest | '−' :: rest => some (.minus, rest)
  | '!' :: rest => some (.deref, rest)
  | ';' :: rest => some (.seq, rest)
  | ':' :: rest => some (.colon, rest)
  | '=' :: rest => some (.equals, rest)
  | '→' :: rest => some (.arrow, rest)
  | '{' :: rest => some (.openBrace, rest)
  | '}' :: rest => some (.closeBrace, rest)
  | ',' :: rest => some (.comma, rest)
  | '.' :: rest => some (.dot, rest)
  | '|' :: rest => some (.bar, rest)
  | '*' :: rest | '∗' :: rest => some (.product, rest)
  | _ => none

/-- Scan a whitespace-free chunk. Each recursive call consumes at least one
character, so the chunk's character count supplies enough fuel. -/
def scan : Nat → List Char → Option (List Token)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, c :: cs => do
    if wordChar c then
      let token ← classifyWord (c :: cs.takeWhile wordChar)
      let rest ← scan fuel (cs.dropWhile wordChar)
      return token :: rest
    else
      let (symbol, tail) ← readPunct (c :: cs)
      let rest ← scan fuel tail
      return .punct symbol :: rest

def whitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def scanChunks : List (List Char) → Option (List Token)
  | [] => some []
  | chunk :: chunks => do
    let here ← scan chunk.length chunk
    let rest ← scanChunks chunks
    return here ++ rest

def tokenize (bytes : ByteArray) : Option (List Token) := do
  let source ← String.fromUTF8? bytes
  scanChunks (source.toList.splitOnP whitespace)

def Token.chars : Token → List Char
  | .keyword k => k.text.toList
  | .punct p => p.chars
  | .number n => n.repr.toList
  | .location s | .variable s => s.toList

def renderChars : List Token → List Char
  | [] => []
  | [token] => token.chars
  | token :: next :: rest => token.chars ++ ' ' :: renderChars (next :: rest)

def render (tokens : List Token) : ByteArray := (String.ofList (renderChars tokens)).toUTF8

def expect (token : Token) : List Token → Option (List Token)
  | head :: tail => if head = token then some tail else none
  | [] => none

/-- The virtual outer group lets the top-level expression omit parentheses.
The token count plus the virtual delimiters bounds the production depth. -/
def readWhole {α : Type} (reader : Nat → List Token → Option (α × List Token))
    (tokens : List Token) : Option α := do
  let (value, []) ← reader (tokens.length + 2)
    (.punct .openP :: (tokens ++ [.punct .closeP])) | none
  return value

end Silmaril.Courses.Cambridge.Concrete
