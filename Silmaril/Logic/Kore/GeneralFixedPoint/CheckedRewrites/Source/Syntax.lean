module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Thms

@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
open Operational.Text

/-- Guarded-first parser classification, not author intent: a conjunction ending
in a supported predicate (including top) is classified as guarded. Other value
conjunctions remain unguarded. Both cases preserve their operational meaning. -/
inductive Form where
  | guarded | unguarded
  deriving DecidableEq, Repr

structure Raw where
  form : Form
  rewrite : RawRewrite
  deriving Repr

namespace Syntax

def resultSort (expected : String) : Parser Unit := fun ts => do
  let (actual, ts) ← sort ts
  if actual = expected then return ((), ts) else none

/-- Concrete result sorts consume their complete `Name{}` syntax. This is not
BooleanTheory's parser for a bare result-sort scheme parameter. -/
def predicate (result : String) : Nat → Parser BooleanTheory.RawPredicate
  | 0, _ => none
  | n + 1, .name name :: .punctuation '{' :: ts => do
    if name == "\\equals" || name == "\\in" then do
      let (input, ts) ← sort ts
      let (_, ts) ← punct ',' ts
      let (_, ts) ← resultSort result ts
      let (_, ts) ← punct '}' ts
      let (_, ts) ← punct '(' ts
      let (p, ts) ← GeneralFixedPoint.Syntax.pattern n ts
      let (_, ts) ← punct ',' ts
      let (q, ts) ← GeneralFixedPoint.Syntax.pattern n ts
      let (_, ts) ← punct ')' ts
      return (if name == "\\equals" then .equal input p q else .member input p q, ts)
    else do
      let (_, ts) ← resultSort result ts
      let (_, ts) ← punct '}' ts
      let (_, ts) ← punct '(' ts
      match name with
      | "\\top" | "\\bottom" =>
          let (_, ts) ← punct ')' ts
          return (if name == "\\top" then .top else .bottom, ts)
      | "\\not" =>
          let (p, ts) ← predicate result n ts
          let (_, ts) ← punct ')' ts
          return (.neg p, ts)
      | "\\and" | "\\or" =>
          let (p, ts) ← predicate result n ts
          let (_, ts) ← punct ',' ts
          let (q, ts) ← predicate result n ts
          let (_, ts) ← punct ')' ts
          return (if name == "\\and" then .conj p q else .disj p q, ts)
      | "\\exists" =>
          let (name, ts) ← identifier ts
          let (_, ts) ← punct ':' ts
          let (bound, ts) ← sort ts
          let (_, ts) ← punct ',' ts
          let (p, ts) ← predicate result n ts
          let (_, ts) ← punct ')' ts
          return (.ex name bound p, ts)
      | _ => none
  | _ + 1, _ => none

def guardedLhs (cfg : String) (fuel : Nat) :
    Parser (RawPattern × BooleanTheory.RawPredicate) := fun ts => do
  let (_, ts) ← word "\\and" ts
  let (_, ts) ← punct '{' ts
  let (_, ts) ← resultSort cfg ts
  let (_, ts) ← punct '}' ts
  let (_, ts) ← punct '(' ts
  let (lhs, ts) ← GeneralFixedPoint.Syntax.pattern fuel ts
  let (_, ts) ← punct ',' ts
  let (guard, ts) ← predicate cfg fuel ts
  let (_, ts) ← punct ')' ts
  return ((lhs, guard), ts)

/-- Read an entire rewrite body. Failed guarded parsing retries the original
stream as an unguarded value pattern, never retaining partial consumption. -/
def rewrite (fuel : Nat) : Parser Raw := fun ts => do
  let (_, ts) ← word "\\rewrites" ts
  let (_, ts) ← punct '{' ts
  let (cfg, ts) ← sort ts
  let (_, ts) ← punct '}' ts
  let (_, ts) ← punct '(' ts
  let (form, lhs, guard, ts) ←
    match guardedLhs cfg fuel ts with
    | some ((lhs, guard), rest) => some (Form.guarded, lhs, guard, rest)
    | none => do
        let (lhs, rest) ← GeneralFixedPoint.Syntax.pattern fuel ts
        some (Form.unguarded, lhs, .top, rest)
  let (_, ts) ← punct ',' ts
  let (rhs, ts) ← GeneralFixedPoint.Syntax.pattern fuel ts
  let (_, ts) ← punct ')' ts
  return (⟨form, ⟨cfg, lhs, guard, rhs⟩⟩, ts)

/-- Existing complete envelope lexer/reader; unsupported attributes, aliases
and hooks remain rejected by the checked payload policy. -/
def parse (text : String) : Option (Kore.Modules.Definition Raw) := do
  let ts ← Kore.FixedPoint.Syntax.lex (text.toList.length + 1) text.toList []
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  let ms ← Kore.Modules.Syntax.modulesWith rewrite ts.length (ts.length + 1) rest
  if ms.isEmpty then none else some ⟨ms⟩

end Syntax
end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
