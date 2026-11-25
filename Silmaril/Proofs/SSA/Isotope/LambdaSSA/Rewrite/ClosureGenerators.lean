module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Forwarding

/-! # The two additional rules are instances of native label substitution -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (liftN liftN_lt liftN_add_index)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem letValue_instance {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {a : Tm Φ} {A : τ}
    (ha : Tm.BranchValue Γ a A) (hr : Region.HasType (A :: Γ) r L) :
    ∃ (x y : Region Φ) (σ : Nat → Region Φ),
      RewriteEquiv Γ x y [A] ∧ LSubst.HasType Γ [A] L σ ∧
      x.lsubst σ = .let₁ a r ∧ y.lsubst σ = r.substVars (Tm.singleSubst a) := by
  let σ : Nat → Region Φ := fun _ => r
  refine ⟨.let₁ a (.br 0 (.var 0)), .br 0 a, σ, .letBr ha (.var rfl) rfl, ?_, ?_, rfl⟩
  · intro ℓ B hℓ
    cases ℓ with
    | zero =>
        cases Option.some.inj hℓ
        exact hr
    | succ ℓ => simp [At] at hℓ
  · change Region.let₁ a (compLSubst labelId σ 0) = _
    rw [compLSubst_id_left]

theorem cfgOutward_instance {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (R : Fin (n + 1) → τ) (hr : Region.HasType Γ r L)
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ (x y : Region Φ) (σ : Nat → Region Φ),
      RewriteEquiv Γ x y (Silmaril.unit :: L) ∧ LSubst.HasType Γ (Silmaril.unit :: L) L σ ∧
      x.lsubst σ = .cfg (r.renameLabels (fun j => n + 1 + j)) (n + 1) blocks ∧ y.lsubst σ = r := by
  let σ : Nat → Region Φ
    | 0 => r.renameVars Nat.succ
    | ℓ + 1 => labelId ℓ
  let ρ := liftN (n + 1) Nat.succ
  have hρ : Ren (List.ofFn R ++ L) (List.ofFn R ++ (Silmaril.unit :: L)) ρ := by
    simpa only [ρ, List.length_ofFn] using (Silmaril.Isotope.SSA.Ren.wk L Silmaril.unit).append (List.ofFn R)
  have hσ : LSubst.HasType Γ (Silmaril.unit :: L) L σ := by
    intro ℓ A hℓ
    cases ℓ with
    | zero =>
        cases Option.some.inj hℓ
        exact hr.renameVars (Silmaril.Isotope.SSA.Ren.wk Γ Silmaril.unit)
    | succ ℓ => exact .br hℓ (.var rfl)
  have hblockSubst : liftLSubstN (n + 1) σ ∘ ρ = labelId := by
    funext ℓ
    by_cases hi : ℓ < n + 1
    · simp only [Function.comp_apply, ρ, liftN_lt Nat.succ hi, liftAtLocal σ hi]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
      simp only [Function.comp_apply, ρ, liftN_add_index, liftAtExit]
      rfl
  have hsubst : Tm.singleSubst (.unit : Tm Φ) ∘ Nat.succ = Tm.var := rfl
  have hid : (σ 0).substVars (Tm.singleSubst .unit) = r := by
    change (r.renameVars Nat.succ).substVars (Tm.singleSubst .unit) = r
    rw [substVars_renameVars, hsubst, substVars_var]
  refine ⟨_, _, σ,
    .entry (.cfgBrExit R (ℓ := 0) rfl .unit (fun i => (hb i).renameLabels hρ)), hσ, ?_, hid⟩
  simp only [lsubst, liftAtExit, substVars_renameLabels, hid, lsubst_renameLabels,
    ← liftLSubstVars_comp_rename, hblockSubst, liftLSubstVars_labelId, lsubst_labelId]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
