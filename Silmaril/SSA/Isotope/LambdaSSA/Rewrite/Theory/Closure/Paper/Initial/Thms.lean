module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Initial

/-! # Structural initiality in Paper -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory.Limits Paper.TypeCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A case on a sum variable can copy a computation into both arms,
with both payload binders unused, in standard Paper. -/
theorem case_ignoring {A B : τ} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {i : Nat} (hi : At Γ i (Silmaril.coprod A B)) (hr : Region.HasType Γ r L) :
    Paper.Eqv Γ (.case (.var i) (r.renameVars Nat.succ) (r.renameVars Nat.succ)) r L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Initial.case_ignoring hi hr

/-- A structurally empty input slot makes all typed regions at that interface equivalent. -/
theorem StructurallyEmpty.eqv_of_empty_slot {P : τ} (hP : StructurallyEmpty P)
    {Γ : VCtx τ} {L : LCtx τ} {i : Nat} (hi : At Γ i P) {r s : Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) : Eqv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Initial.eqv_of_empty_slot hP hi hr hs

/-- Structural emptiness entails initiality in the guarded singleton category. -/
theorem StructurallyEmpty.initial {P : τ} (hP : StructurallyEmpty P) :
    Nonempty (IsInitial (ofType (Φ := Φ) P)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Initial.initial hP

end Silmaril.Isotope.LambdaSSA.Region.Paper
