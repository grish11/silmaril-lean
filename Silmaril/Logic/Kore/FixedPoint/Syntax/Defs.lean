module

public import Silmaril.Logic.Kore.Operational.Text.Defs

/-! Named positive patterns from the pinned KORE grammar. This is a separate
pattern reader, not an extension of the existing complete module checker. -/
@[expose] public section
namespace Silmaril.Logic.Kore.FixedPoint

inductive RawPattern where
  | evar (name sort : String)
  | svar (name sort : String)
  | app (name : String) (arguments : List RawPattern)
  | top (sort : String)
  | bottom (sort : String)
  | conj (sort : String) (left right : RawPattern)
  | disj (sort : String) (left right : RawPattern)
  | ex (sort name bound : String) (body : RawPattern)
  | all (sort name bound : String) (body : RawPattern)
  | mu (name sort : String) (body : RawPattern)
  | nu (name sort : String) (body : RawPattern)
  deriving Repr

namespace Syntax
open Operational.Text

/-- The existing ASCII lexer with a local set-variable branch. Comments and
strings use the existing readers; the old frontend's acceptance is unchanged. -/
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
  | n + 1, '@' :: c :: rest, acc =>
      if letter c then
        let (tail, rest) := rest.span nameChar
        if keyword (String.ofList (c :: tail)) then none else
        lex n rest (.name (String.ofList ('@' :: c :: tail)) :: acc)
      else none
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

def ordinary (name : String) : Bool :=
  !keyword name && name.toList.head?.any letter

def sort : Parser String := fun ts => do
  let (name, rest) ← Operational.Text.sort ts
  if ordinary name then some (name, rest) else none

def makeNode (name : String) (sorts : List String) (args : List RawPattern) :
    Option RawPattern :=
  match name, sorts, args with
  | "\\top", [s], [] => some (.top s)
  | "\\bottom", [s], [] => some (.bottom s)
  | "\\and", [s], [p, q] => some (.conj s p q)
  | "\\or", [s], [p, q] => some (.disj s p q)
  | "\\exists", [s], [.evar n b, p] => some (.ex s n b p)
  | "\\forall", [s], [.evar n b, p] => some (.all s n b p)
  | "\\mu", [], [.svar n s, p] => some (.mu n s p)
  | "\\nu", [], [.svar n s, p] => some (.nu n s p)
  | _, [], args => if ordinary name then some (.app name args) else none
  | _, _, _ => none

def patternWith {P : Type} (makeVariable : Bool → String → String → P)
    (node : String → List String → List P → Option P) : Nat → Parser P
  | 0, _ => none
  | _ + 1, .name name :: .punctuation ':' :: ts => do
      let (s, rest) ← sort ts
      if name.toList.head? == some '@' then return (makeVariable true name s, rest)
      else if ordinary name then return (makeVariable false name s, rest)
      else none
  | n + 1, .name name :: .punctuation '{' :: ts => do
      let (sorts, ts) ← list sort '}' (n + 1) ts
      let (_, ts) ← punct '(' ts
      let (args, rest) ← list (patternWith makeVariable node n) ')' (n + 1) ts
      return (← node name sorts args, rest)
  | _ + 1, _ => none

abbrev pattern := patternWith (fun isSet name s =>
  if isSet then RawPattern.svar name s else RawPattern.evar name s) makeNode

/-- Complete pattern input: unsupported builtins and trailing tokens reject. -/
def parse (text : String) : Option RawPattern := do
  let ts ← lex (text.toList.length + 1) text.toList []
  let (p, rest) ← pattern (ts.length + 1) ts
  if rest.isEmpty then some p else none
end Syntax
end Silmaril.Logic.Kore.FixedPoint
