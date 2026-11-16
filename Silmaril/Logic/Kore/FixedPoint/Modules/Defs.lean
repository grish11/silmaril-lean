module

public import Silmaril.Logic.Kore.FixedPoint.Institution.Defs
public import Silmaril.Logic.Kore.Modules.Theory.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.FixedPoint
open CategoryTheory

namespace Checking

/-- Collect free names independently in the two namespaces. Elaboration checks
all occurrences against the resulting nearest-name sorted contexts. -/
def freeNames (setVariables : Bool) : Nat → List String → RawPattern → Names
  | 0, _, _ => []
  | _ + 1, bound, .evar n s =>
      if !setVariables && !bound.contains n then [(n, s)] else []
  | _ + 1, bound, .svar n s =>
      if setVariables && !bound.contains n then [(n, s)] else []
  | n + 1, bound, .app _ ps => ps.flatMap (freeNames setVariables n bound)
  | _ + 1, _, .top _ | _ + 1, _, .bottom _ => []
  | n + 1, bound, .conj _ p q | n + 1, bound, .disj _ p q =>
      freeNames setVariables n bound p ++ freeNames setVariables n bound q
  | n + 1, bound, .ex _ name _ p | n + 1, bound, .all _ name _ p =>
      freeNames setVariables n (if setVariables then bound else name :: bound) p
  | n + 1, bound, .mu name _ p | n + 1, bound, .nu name _ p =>
      freeNames setVariables n (if setVariables then name :: bound else bound) p

def resultSort (scope : Modules.Scope) : RawPattern → Option String
  | .evar _ s | .svar _ s | .top s | .bottom s | .conj s _ _ | .disj s _ _
  | .ex s _ _ _ | .all s _ _ _ | .mu _ s _ | .nu _ s _ => some s
  | .app name _ => (scope.symbols.find? (fun d => d.declaration.name == name)).map
      (fun d => d.declaration.result)

def checkedSentence (scope : Modules.Scope) (fuel : Nat) (raw : RawPattern) :
    Option (CheckedSentence scope) := do
  let sets := (freeNames true fuel [] raw).eraseDups
  let objects := (freeNames false fuel [] raw).eraseDups
  let s ← resultSort scope raw
  match accepted : elaborate scope fuel sets objects s raw with
  | none => none
  | some typed => some ⟨fuel, sets, objects, s, raw, typed, accepted⟩

/-- Install actual checked source syntax at its declaration-backed signature. -/
def sentence (scope : Modules.Scope) (fuel : Nat) (raw : RawPattern) :
    Option (Sentence scope.signature) := do
  return (← checkedSentence scope fuel raw).install

/-- Unlike the first-order profile, this positive profile rejects aliases. -/
def visible (scope : Modules.Scope) : Nat → RawPattern → Bool
  | 0, _ => false
  | _ + 1, .evar _ s | _ + 1, .svar _ s | _ + 1, .top s | _ + 1, .bottom s =>
      Modules.Checking.namedSort scope s
  | n + 1, .app name ps =>
      scope.symbols.any (fun d => d.declaration.name == name) && ps.all (visible scope n)
  | n + 1, .conj s p q | n + 1, .disj s p q =>
      Modules.Checking.namedSort scope s && visible scope n p && visible scope n q
  | n + 1, .ex s _ b p | n + 1, .all s _ b p =>
      Modules.Checking.namedSort scope s && Modules.Checking.namedSort scope b && visible scope n p
  | n + 1, .mu _ s p | n + 1, .nu _ s p =>
      Modules.Checking.namedSort scope s && visible scope n p

def profile : Modules.Checking.SentenceProfile :=
  ⟨RawPattern, institution, sentence, visible, false⟩
end Checking

namespace Modules

/-- Use the shared complete module envelope with the positive pattern parser.
The local lexer adds set names; attributes and unsupported constructs still reject. -/
def parse (text : String) : Option (Kore.Modules.Definition RawPattern) := do
  let ts ← Syntax.lex (text.toList.length + 1) text.toList []
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  let ms ← Kore.Modules.Syntax.modulesWith Syntax.pattern ts.length (ts.length + 1) rest
  if ms.isEmpty then none else some ⟨ms⟩

abbrev CheckedDefinition := Kore.Modules.Checking.CheckedDefinition Checking.profile
abbrev CheckedModule (scope : Kore.Modules.Scope) :=
  Kore.Modules.Checking.CheckedModule scope Checking.profile

def checkText (fuel : Nat) (text : String) : Option CheckedDefinition := do
  Kore.Modules.Checking.checkDefinitionWith Checking.profile fuel (← parse text)

end Modules
end Silmaril.Logic.Kore.FixedPoint
