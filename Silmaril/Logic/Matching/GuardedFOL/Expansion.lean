module

public import Silmaril.Logic.Matching.GuardedFOL.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedFOL
open CategoryTheory Silmaril.Logic.Institution.Examples

abbrev paddedCarrier {S : FOL.Signature} (M : FOL.Structure S) : MatchingSort S → Type
  | .object s => Option (M.carrier s)
  | .truth => Unit

/-- A native matching model with actual Option carriers, not a lifted truth predicate. -/
abbrev rawExpansion {S : FOL.Signature} (M : FOL.Structure S) : FirstOrder.Model (signature S).symbols where
  carrier := paddedCarrier M
  nonempty s := match s with | .object _ => ⟨none⟩ | .truth => ⟨()⟩
  operation op args := match op with
    | .function o => {y | ∃ values, (∀ i, args i = some (values i)) ∧ y = some (M.op o values)}
    | @Operation.relation _ n inputs r => {_result | ∃ values : ∀ i, M.carrier (inputs i),
        (∀ i, args i = some (values i)) ∧ M.rel r values}
    | .active _ => Set.range some
    | .defined _ => Set.univ
    | .truth => Set.univ

def unpad {S : FOL.Signature} {M : FOL.Structure S} {s : S.S}
    (x : Active (rawExpansion M) s) : M.carrier s := Classical.choose x.property

theorem unpad_spec {S : FOL.Signature} {M : FOL.Structure S} {s : S.S}
    (x : Active (rawExpansion M) s) : some (unpad x) = x.val := Classical.choose_spec x.property

/-- All raw graph constraints are proved from the original FOL operations. -/
abbrev expand {S : FOL.Signature} (M : FOL.Structure S) : Model S where
  base := rawExpansion M
  function op args := by
    let values := fun i => unpad (args i)
    refine ⟨⟨some (M.op op values), ⟨M.op op values, rfl⟩⟩, ?_⟩
    apply Set.ext
    intro y
    constructor
    · rintro ⟨other, ho, rfl⟩
      have same : other = values := funext fun i => Option.some.inj ((ho i).symm.trans (unpad_spec (args i)).symm)
      exact congrArg (fun vs => some (M.op op vs)) same
    · intro hy
      exact ⟨values, fun i => (unpad_spec (args i)).symm, hy⟩
  relation r args := by
    classical
    by_cases h : ∃ values, (∀ i, args i = some (values i)) ∧ M.rel r values
    · exact Or.inr (Set.ext fun _ => ⟨fun _ => trivial, fun _ => h⟩)
    · exact Or.inl (Set.ext fun _ => ⟨fun hx => h hx, False.elim⟩)
  definedness _ _ := rfl
  truth _ := rfl

/-- Canonical expansion has an actual equivalence of active and source carriers,
including empty sorts. It does not identify these types by equality. -/
def activeEquiv {S : FOL.Signature} (M : FOL.Structure S) (s : S.S) : Active (expand M).base s ≃ M.carrier s where
  toFun := unpad
  invFun x := ⟨some x, ⟨x, rfl⟩⟩
  left_inv x := Subtype.ext (unpad_spec x)
  right_inv x := Option.some.inj (unpad_spec ⟨some x, ⟨x, rfl⟩⟩)
end Silmaril.Logic.Matching.GuardedFOL
