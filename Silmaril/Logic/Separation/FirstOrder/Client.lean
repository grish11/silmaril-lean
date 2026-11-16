module

public import Silmaril.Logic.Separation.FirstOrder.Thms
public import Silmaril.Logic.Separation.FirstOrder.Symbols

/-! A complete checked client of the fixed-sort owned-store encoding. -/
@[expose] public section
namespace Silmaril.Logic.Separation.FirstOrder.Client
open Silmaril.Logic.Institution.Examples
open Examples

/-- Arbitrary open formulas, not just closed examples. -/
example {A : FOL.Signature} (M : FOL.Structure A) {k} {Γ : Fin k → A.S}
    (φ : FOL.Formula A Γ) (ρ : ∀ i, M.carrier (Γ i)) :
    store M Γ ρ ∈ (compile φ).denote (native M) ↔ φ.Holds M ρ :=
  compile_correct M φ ρ

example : different.Holds (pureModel Bool) := bool_different
example : ¬ different.Holds (pureModel Unit) := unit_not_different
example : different.Holds (pureModel Empty) := empty_different

example : (sentence different).Satisfies (native (pureModel Bool)) :=
  bool_native_different

example : ¬ (sentence collapse).Satisfies (native (pureModel Bool)) :=
  bool_native_not_collapse

/-- Reusing a slot incorrectly validates the false Bool collapse statement. -/
example : (⟨.emp, duplicated⟩ : BaseSentence (signature pure.fol)).Satisfies
    (native (pureModel Bool)) := duplicated_native_true

example : ¬ Function.Injective (squash.map ()) := squash_not_injective

example : native ((FOL.Structure.reduct identify.fol).obj symbolModel) =
    Separation.reduct (atomMap identify) (native symbolModel) := symbol_reduct_exact

/-- The canonical target restriction matters even for reflexivity. -/
example : ¬ (sentence reflexive).Satisfies badNative := unrestricted_reflexive_failure

end Silmaril.Logic.Separation.FirstOrder.Client
