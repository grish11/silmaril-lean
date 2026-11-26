module

public import Init.Data.List.TakeDrop

@[expose] public section

namespace Silmaril.Machine.SQLite.Tokenizer

/-- The lexical alphabet of the point-read fragment. Words use lowercase ASCII spelling
after tokenization. The parser interprets them as grammar words or catalog names. -/
inductive Token where
  | word (spelling : String)
  | equals
  | parameterOne
  | semicolon
  deriving DecidableEq, Repr

inductive Error where
  | outsideFragment
  deriving DecidableEq, Repr

def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'

def isWordStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

def isWordContinue (c : Char) : Bool :=
  isWordStart c || c.isDigit

def normalize (chars : List Char) : String :=
  String.ofList (chars.map Char.toLower)

/-- The spelling of a normalized word accepted by the scanner. -/
def CanonicalWord (word : String) : Prop :=
  match word.toList with
  | [] => False
  | c :: rest =>
    isWordStart c = true ∧ rest.all isWordContinue = true ∧ normalize (c :: rest) = word

instance (word : String) : Decidable (CanonicalWord word) := by
  unfold CanonicalWord
  split <;> infer_instance

def Token.Canonical : Token → Prop
  | .word spelling => CanonicalWord spelling
  | _ => True

instance (token : Token) : Decidable token.Canonical := by
  cases token <;> unfold Token.Canonical <;> infer_instance

/-- A normalized token spelling. Word tokens supplied by callers should be canonical. -/
def Token.chars : Token → List Char
  | .word spelling => spelling.toList
  | .equals => ['=']
  | .parameterOne => ['?', '1']
  | .semicolon => [';']

/-- Separate each token with ASCII space, including after the last token. -/
def render : List Token → List Char
  | [] => []
  | t :: rest => t.chars ++ ' ' :: render rest

/-- The concrete scanner state is the unread character suffix. -/
abbrev State := List Char

/-- Lexical judgment for the scoped text. A word consumes the maximal run
of continuation characters. Layout characters have no token. -/
inductive Lexes : State → List Token → Prop where
  | done : Lexes [] []
  | space {c rest tokens} (h : isSpace c = true) (tail : Lexes rest tokens) :
      Lexes (c :: rest) tokens
  | word {c rest tokens} (h : isWordStart c = true)
      (tail : Lexes (rest.dropWhile isWordContinue) tokens) :
      Lexes (c :: rest) (.word (normalize (c :: rest.takeWhile isWordContinue)) :: tokens)
  | equals {rest tokens} (tail : Lexes rest tokens) :
      Lexes ('=' :: rest) (.equals :: tokens)
  | parameterOne {rest tokens} (tail : Lexes rest tokens) :
      Lexes ('?' :: '1' :: rest) (.parameterOne :: tokens)
  | semicolon {rest tokens} (tail : Lexes rest tokens) :
      Lexes (';' :: rest) (.semicolon :: tokens)

/-- Scan one complete input. A character outside the lexical alphabet, including a
question mark without the literal one that this profile consumes, rejects the input. -/
def scan (input : State) : Except Error (List Token) :=
  match input with
  | [] => .ok []
  | c :: rest =>
    if isSpace c then scan rest
    else if isWordStart c then
      let word := normalize (c :: rest.takeWhile isWordContinue)
      (scan (rest.dropWhile isWordContinue)).map (.word word :: ·)
    else
      match c, rest with
      | '=', rest => (scan rest).map (.equals :: ·)
      | '?', '1' :: rest => (scan rest).map (.parameterOne :: ·)
      | ';', rest => (scan rest).map (.semicolon :: ·)
      | _, _ => .error .outsideFragment
termination_by input.length
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | have splitLength :=
        congrArg List.length (List.takeWhile_append_dropWhile (p := isWordContinue) (l := rest))
      simp only [List.length_append] at splitLength
      omega

def tokenize (text : String) : Except Error (List Token) :=
  scan text.toList

end Silmaril.Machine.SQLite.Tokenizer
