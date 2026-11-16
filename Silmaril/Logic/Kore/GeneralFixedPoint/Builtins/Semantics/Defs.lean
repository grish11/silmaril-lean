module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Checking.Defs
public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Semantics.Defs

/-! Independent original raw denotation. Domain values denote the actual
Bool/Int carrier elements, not the denotation of any generated operation or
compiler result. Imports contribute declarations; aliases keep original bodies.
Fixed points are full prefixed and postfixed set intersections/unions. -/
-- Configurable builtin names intentionally have a canonical fallback instance.
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics
variable [sorts : SortBindings]
open Kore.Modules.Checking
abbrev Values := @GeneralFixedPoint.Semantics.Values
abbrev lookupValue := @GeneralFixedPoint.Semantics.lookupValue
abbrev interpret := @GeneralFixedPoint.Semantics.interpret

def denote (scope : Modules.Scope) (aliases : List Alias) (M : Matching.GeneralFixedPoint.Model scope.signature)
    (B : Carriers M) :
    Nat → Values M → Values M → (s : String) → RawPattern → Option (Set (M.carrier s))
  | 0, _, _, _, _ => none
  | _ + 1, _, _, s, .domainValue actual text => do
      if actual ≠ s then none else do
        let l ← Literal.parse actual text
        if same : l.sort = s then some (same ▸ {B.literal l}) else none
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
      return (← denote scope aliases M B n sets objects s p)ᶜ
  | n + 1, sets, objects, s, .conj actual p q => do
      if actual ≠ s then none else
      return (← denote scope aliases M B n sets objects s p) ∩ (← denote scope aliases M B n sets objects s q)
  | n + 1, sets, objects, s, .disj actual p q => do
      if actual ≠ s then none else
      return (← denote scope aliases M B n sets objects s p) ∪ (← denote scope aliases M B n sets objects s q)
  | n + 1, sets, objects, s, .ex actual name b p =>
      if actual ≠ s || !namedSort scope b then none else
      some {x | ∃ a : M.carrier b,
        x ∈ (denote scope aliases M B n sets (⟨name, b, {a}⟩ :: objects) s p).getD ∅}
  | n + 1, sets, objects, s, .all actual name b p =>
      if actual ≠ s || !namedSort scope b then none else
      some {x | ∀ a : M.carrier b,
        x ∈ (denote scope aliases M B n sets (⟨name, b, {a}⟩ :: objects) s p).getD ∅}
  | n + 1, sets, objects, s, .mu name actual p =>
      if actual ≠ s || !namedSort scope s then none else
      some (sInf {X | (denote scope aliases M B n (⟨name, s, X⟩ :: sets) objects s p).getD ∅ ⊆ X})
  | n + 1, sets, objects, s, .nu name actual p =>
      if actual ≠ s || !namedSort scope s then none else
      some (sSup {X | X ⊆ (denote scope aliases M B n (⟨name, s, X⟩ :: sets) objects s p).getD ∅})
  | n + 1, sets, objects, s, .app name args => do
      match scope.symbols.attach.find? (fun d => d.val.declaration.name == name) with
      | some d => do
          if h : d.val.declaration.result = s then
            if len : args.length = d.val.declaration.arguments.length then do
              let ps ← collect (fun i : Fin d.val.declaration.arguments.length =>
                denote scope aliases M B n sets objects (d.val.declaration.arguments.get i)
                  (args.get ⟨i.val, by omega⟩))
              let op : scope.signature.operations _ (fun i => d.val.declaration.arguments.get i) s :=
                ⟨d.val, d.property, by simp, h⟩
              return {result | ∃ values, (∀ i, values i ∈ ps i) ∧ result ∈ M.operation op values}
            else none
          else none
      | none => do
          let d ← aliases.find? (fun d => d.symbol.name == name)
          if d.valid scope && d.symbol.result == s && args.length == d.parameters.length then do
            let σ ← collect (fun i : Fin (d.names false).length => do
              let arg ← d.argument args false ((d.names false).get i).1
              denote scope aliases M B n sets objects (context (d.names false) i) arg)
            let τ ← collect (fun i : Fin (d.names true).length => do
              let arg ← d.argument args true ((d.names true).get i).1
              denote scope aliases M B n sets objects (context (d.names true) i) arg)
            denote scope aliases M B n (interpret M (d.names true) τ)
              (interpret M (d.names false) σ) s d.body
          else none

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Semantics
