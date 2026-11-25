module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueFamilies

/-! # Stability of continuation families under native substitution -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem LSubst.ValueFamily.id (Γ : VCtx τ) (L : LCtx τ) :
    LSubst.ValueFamily (Φ := Φ) Γ L L labelId :=
  fun _ _ h => .br h (.var rfl)

theorem LSubst.ValueFamily.comp {Γ : VCtx τ} {L K P : LCtx τ} {σ υ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) (hυ : LSubst.ValueFamily Γ K P υ) :
    LSubst.ValueFamily Γ L P (compLSubst σ υ) :=
  fun _ A h => Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueBranches_lsubst (hσ h)
    (Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueFamily_liftVars hυ A)

end Silmaril.Isotope.LambdaSSA.Region
