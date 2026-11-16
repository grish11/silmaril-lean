module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Checking.Defs
public import Silmaril.Logic.Kore.FixedPoint.Semantics.Defs

/-! Independent raw set interpretation. Fixed points are intersections of
pre-fixed sets and unions of post-fixed sets, defined without calling the
checker, lowering, or native pattern interpretation. Unsupported subterms use
the empty set under binders; adequacy is asserted only after successful checking. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Semantics
open Modules.Checking

abbrev Values {scope : Modules.Scope} (M : Matching.GeneralFixedPoint.Model scope.signature) :=
  FixedPoint.Semantics.Values M
abbrev lookupValue {scope : Modules.Scope} (M : Matching.GeneralFixedPoint.Model scope.signature) :=
  FixedPoint.Semantics.lookupValue M
abbrev interpret {scope : Modules.Scope} (M : Matching.GeneralFixedPoint.Model scope.signature) :=
  FixedPoint.Semantics.interpret M

def denote (scope : Modules.Scope) (M : Matching.GeneralFixedPoint.Model scope.signature) :
    Nat → Values M → Values M → (s : String) → RawPattern → Option (Set (M.carrier s))
  | 0, _, _, _, _ => none
  | _ + 1, _, _, _, .domainValue _ _ => none
  | _ + 1, _, objects, s, .evar name actual =>
      if actual ≠ s || !namedSort scope s then none else lookupValue M objects name s
  | _ + 1, sets, _, s, .svar name actual =>
      if actual ≠ s || !namedSort scope s then none else lookupValue M sets name s
  | _ + 1, _, _, s, .top actual =>
      if actual = s && namedSort scope s then some Set.univ else none
  | _ + 1, _, _, s, .bottom actual =>
      if actual = s && namedSort scope s then some ∅ else none
  | n + 1, sets, objects, s, .neg actual p => do
      if actual ≠ s then none else
      return (← denote scope M n sets objects s p)ᶜ
  | n + 1, sets, objects, s, .conj actual p q => do
      if actual ≠ s then none else
      return (← denote scope M n sets objects s p) ∩ (← denote scope M n sets objects s q)
  | n + 1, sets, objects, s, .disj actual p q => do
      if actual ≠ s then none else
      return (← denote scope M n sets objects s p) ∪ (← denote scope M n sets objects s q)
  | n + 1, sets, objects, s, .ex actual name b p =>
      if actual ≠ s || !namedSort scope b then none else
      some {x | ∃ a : M.carrier b,
        x ∈ (denote scope M n sets (⟨name, b, {a}⟩ :: objects) s p).getD ∅}
  | n + 1, sets, objects, s, .all actual name b p =>
      if actual ≠ s || !namedSort scope b then none else
      some {x | ∀ a : M.carrier b,
        x ∈ (denote scope M n sets (⟨name, b, {a}⟩ :: objects) s p).getD ∅}
  | n + 1, sets, objects, s, .mu name actual p =>
      if actual ≠ s || !namedSort scope s then none else
      some (sInf {X | (denote scope M n (⟨name, s, X⟩ :: sets) objects s p).getD ∅ ⊆ X})
  | n + 1, sets, objects, s, .nu name actual p =>
      if actual ≠ s || !namedSort scope s then none else
      some (sSup {X | X ⊆ (denote scope M n (⟨name, s, X⟩ :: sets) objects s p).getD ∅})
  | n + 1, sets, objects, s, .app name args => do
      let d ← scope.symbols.attach.find? (fun d => d.val.declaration.name == name)
      if h : d.val.declaration.result = s then
        if len : args.length = d.val.declaration.arguments.length then do
          let ps ← collect (fun i : Fin d.val.declaration.arguments.length =>
            denote scope M n sets objects (d.val.declaration.arguments.get i)
              (args.get ⟨i.val, by omega⟩))
          let op : scope.signature.operations _ (fun i => d.val.declaration.arguments.get i) s :=
            ⟨d.val, d.property, by simp, h⟩
          return {result | ∃ values, (∀ i, values i ∈ ps i) ∧ result ∈ M.operation op values}
        else none
      else none
/-- Interpret complete source text independently of elaboration. -/
def read (scope : Modules.Scope) (M : Matching.GeneralFixedPoint.Model scope.signature)
    (fuel : Nat) (sets objects : Values M) (s text : String) : Option (Set (M.carrier s)) := do
  denote scope M fuel sets objects s (← Syntax.parse text)
end Silmaril.Logic.Kore.GeneralFixedPoint.Semantics
