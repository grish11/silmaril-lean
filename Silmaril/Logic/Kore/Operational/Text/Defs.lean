module

public import Silmaril.Logic.Kore.Operational.Defs

/-! A total, fuel-bounded reader for the concrete KORE operational profile.
The lexer follows the pinned ASCII identifier, comment and string grammar.
The parser retains alias signatures, left sides and metadata before checking
the operational profile. Unsupported input fails the complete read. -/

@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Text

inductive Token where
  | name (value : String)
  | literal (value : String)
  | punctuation (value : Char)
  deriving DecidableEq, Repr

def letter (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')

def nameChar (c : Char) : Bool :=
  letter c || ('0' ≤ c && c ≤ '9') || c == '\'' || c == '-'

def whitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 12

def keyword (s : String) : Bool :=
  ["module", "endmodule", "import", "sort", "hooked-sort", "symbol",
   "hooked-symbol", "axiom", "claim", "alias", "where"].contains s

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def readHex : Nat → Nat → List Char → Option (Nat × List Char)
  | 0, value, rest => some (value, rest)
  | n + 1, value, c :: rest => do
      let digit ← hexDigit c
      readHex n (16 * value + digit) rest
  | _ + 1, _, [] => none

def codepoint (n : Nat) : Option Char :=
  if n ≤ 0x10ffff ∧ ¬ (0xd800 ≤ n ∧ n ≤ 0xdfff) then some (Char.ofNat n)
  else none

def escape : List Char → Option (Char × List Char)
  | 't' :: rest => some ('\t', rest)
  | 'n' :: rest => some ('\n', rest)
  | 'f' :: rest => some (Char.ofNat 12, rest)
  | 'r' :: rest => some ('\r', rest)
  | '"' :: rest => some ('"', rest)
  | '\\' :: rest => some ('\\', rest)
  | 'x' :: rest => do
      let (n, rest) ← readHex 2 0 rest
      return (← codepoint n, rest)
  | 'u' :: rest => do
      let (n, rest) ← readHex 4 0 rest
      return (← codepoint n, rest)
  | 'U' :: rest => do
      let (n, rest) ← readHex 8 0 rest
      return (← codepoint n, rest)
  | _ => none

def readString : Nat → List Char → List Char → Option (String × List Char)
  | 0, _, _ => none
  | _ + 1, '"' :: rest, acc => some (String.ofList acc.reverse, rest)
  | n + 1, '\\' :: rest, acc => do
      let (c, rest) ← escape rest
      readString n rest (c :: acc)
  | n + 1, c :: rest, acc =>
      if 32 ≤ c.toNat ∧ c.toNat ≤ 126 then readString n rest (c :: acc) else none
  | _ + 1, [], _ => none

def skipLine : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => skipLine rest

def skipBlock : List Char → Option (List Char)
  | '*' :: '/' :: rest => some rest
  | _ :: rest => skipBlock rest
  | [] => none

def lex : Nat → List Char → List Token → Option (List Token)
  | 0, _, _ => none
  | _ + 1, [], acc => some acc.reverse
  | n + 1, '/' :: '/' :: rest, acc => lex n (skipLine rest) acc
  | n + 1, '/' :: '*' :: rest, acc => do
      let rest ← skipBlock rest
      lex n rest acc
  | n + 1, '"' :: rest, acc => do
      let (value, rest) ← readString (rest.length + 1) rest []
      lex n rest (.literal value :: acc)
  | n + 1, '\\' :: c :: rest, acc =>
      if letter c then
        let (tail, rest) := rest.span nameChar
        lex n rest (.name (String.ofList ('\\' :: c :: tail)) :: acc)
      else none
  | n + 1, c :: rest, acc =>
      if whitespace c then lex n rest acc
      else if ['{', '}', '(', ')', '[', ']', ',', ':', '='].contains c then
        lex n rest (.punctuation c :: acc)
      else if letter c then
        let (tail, rest) := rest.span nameChar
        lex n rest (.name (String.ofList (c :: tail)) :: acc)
      else none

def tokenize (input : String) : Option (List Token) :=
  lex (input.toList.length + 1) input.toList []

abbrev Parser (α : Type) := List Token → Option (α × List Token)

def punct (c : Char) : Parser Unit
  | .punctuation d :: rest => if c = d then some ((), rest) else none
  | _ => none

def word (expected : String) : Parser Unit
  | .name value :: rest => if value = expected then some ((), rest) else none
  | _ => none

def identifier : Parser String
  | .name value :: rest =>
      if !keyword value && !(value.toList.head? == some '\\') then some (value, rest)
      else none
  | _ => none

def sort : Parser String := fun tokens => do
  let (name, rest) ← identifier tokens
  let (_, rest) ← punct '{' rest
  let (_, rest) ← punct '}' rest
  return (name, rest)

def listTail {α : Type} (parse : Parser α) (closing : Char) :
    Nat → List α → Parser (List α)
  | 0, _, _ => none
  | n + 1, acc, .punctuation c :: rest =>
      if c = closing then some (acc.reverse, rest)
      else if c = ',' then do
        let (a, rest) ← parse rest
        listTail parse closing n (a :: acc) rest
      else none
  | _ + 1, _, _ => none

def list {α : Type} (parse : Parser α) (closing : Char) (fuel : Nat) :
    Parser (List α) := fun tokens => do
  match tokens with
  | .punctuation c :: rest =>
      if c = closing then return ([], rest)
  | _ => pure ()
  let (a, rest) ← parse tokens
  listTail parse closing fuel [a] rest

def node (name : String) (sorts : List String) (args : List Raw) : Option Raw :=
  match name, sorts, args with
  | "\\dv", [s], [.stringLiteral value] => some (.domainValue s value)
  | "\\top", [s], [] => some (.top s)
  | "\\and", [s], [a, b] => some (.and s a b)
  | "\\rewrites", [s], [a, b] => some (.rewrites s a b)
  | "\\equals", [s, t], [a, b] => some (.equals s t a b)
  | "\\next", [s], [a] => some (.next s a)
  | _, _, _ =>
      if name.toList.head? == some '\\' || keyword name then none
      else match args with
        | [] => some (.app0 name sorts)
        | [a] => some (.app1 name sorts a)
        | [a, b] => some (.app2 name sorts a b)
        | _ => none

def raw : Nat → Parser Raw
  | 0, _ => none
  | _ + 1, .literal value :: rest => some (.stringLiteral value, rest)
  | _ + 1, .name name :: .punctuation ':' :: rest => do
      if keyword name || name.toList.head? == some '\\' then none else do
      let (s, rest) ← sort rest
      return (.variable name s, rest)
  | n + 1, .name name :: .punctuation '{' :: rest => do
      let (sorts, rest) ← list sort '}' (n + 1) rest
      let (_, rest) ← punct '(' rest
      let (args, rest) ← list (raw n) ')' (n + 1) rest
      return (← node name sorts args, rest)
  | _ + 1, _ => none

/-- Alias syntax is retained before validation; no declared profile is dropped. -/
structure ParsedAlias where
  name : String
  sortVariables : List String
  argumentSorts : List String
  resultSort : String
  lhs : Raw
  rhs : Raw
  attributes : List Raw
  deriving DecidableEq, Repr

def readAlias (fuel : Nat) : Parser ParsedAlias := fun tokens => do
  let (_, rest) ← word "alias" tokens
  let (name, rest) ← identifier rest
  let (_, rest) ← punct '{' rest
  let (sortVars, rest) ← list identifier '}' fuel rest
  let (_, rest) ← punct '(' rest
  let (arguments, rest) ← list sort ')' fuel rest
  let (_, rest) ← punct ':' rest
  let (result, rest) ← sort rest
  let (_, rest) ← word "where" rest
  let (lhs, rest) ← raw fuel rest
  let (_, rest) ← punct ':' rest
  let (_, rest) ← punct '=' rest
  let (rhs, rest) ← raw fuel rest
  let (_, rest) ← punct '[' rest
  let (attributes, rest) ← list (raw fuel) ']' fuel rest
  return (⟨name, sortVars, arguments, result, lhs, rhs, attributes⟩, rest)

def declaration (fuel : Nat) : Parser Declaration := fun tokens => do
  let (kind, rest) ← match tokens with
    | .name "axiom" :: rest => some (DeclarationKind.ruleAxiom, rest)
    | .name "claim" :: rest => some (DeclarationKind.claim, rest)
    | _ => none
  let (_, rest) ← punct '{' rest
  let (sortVars, rest) ← list identifier '}' fuel rest
  let (body, rest) ← raw fuel rest
  let (_, rest) ← punct '[' rest
  let (attributes, rest) ← list (raw fuel) ']' fuel rest
  return (⟨kind, sortVars, body, attributes⟩, rest)

def declarations : Nat → List Token → Option (List Declaration)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, tokens => do
      let (d, rest) ← declaration (n + 1) tokens
      return d :: (← declarations n rest)

structure ParsedInput where
  aliasDeclaration : ParsedAlias
  declarations : List Declaration
  deriving DecidableEq, Repr

/-- Read one alias followed by complete declarations. No trailing tokens skip. -/
def parse (input : String) : Option ParsedInput := do
  let tokens ← tokenize input
  let (a, rest) ← readAlias (tokens.length + 1) tokens
  return ⟨a, ← declarations (rest.length + 1) rest⟩

/-- Check all alias signature fields, the captured left side and the body. -/
def ParsedAlias.elaborate (a : ParsedAlias) : Option (Context × Alias) := do
  if ["SortGeneratedCounterCell", "SortK", "SortKCell", "SortGeneratedTopCell", "SortState", "SortKItem",
      "Lbl'-LT-'generatedTop'-GT-'", "Lbl'-LT-'k'-GT-'", "kseq", "inj", "label",
      "org'Stop'kframework'Stop'attributes'Stop'Source",
      "org'Stop'kframework'Stop'definition'Stop'Production",
      "org'Stop'kframework'Stop'attributes'Stop'Location", "UNIQUE'Unds'ID"].contains a.name ||
      a.sortVariables != [] ||
      a.argumentSorts != ["SortGeneratedCounterCell", "SortK"] ||
      a.resultSort != "SortGeneratedTopCell" || a.attributes != [] then none else
  match a.lhs with
  | .app2 name [] (.variable counter "SortGeneratedCounterCell") (.variable tail "SortK") =>
      if name != a.name || counter == tail then none else do
      let Γ : Context := ⟨tail, counter⟩
      let _ ← elaborateConfig Γ a.rhs
      return (Γ, ⟨a.name, a.rhs⟩)
  | _ => none

structure CheckedProgram where
  context : Context
  aliasDefinition : Alias
  declarations : List Declaration
  checked : CheckedInput
  deriving DecidableEq, Repr

/-- Compose actual text reading, alias validation and operational checking. -/
def check (input : String) : Option CheckedProgram := do
  let parsed ← parse input
  let (Γ, a) ← parsed.aliasDeclaration.elaborate
  let checked ← checkInput Γ a parsed.declarations
  return ⟨Γ, a, parsed.declarations, checked⟩

end Silmaril.Logic.Kore.Operational.Text
