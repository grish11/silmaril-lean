module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms

/-! # Substitution in the literal entry-let schema -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplay

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet (Step)
open Silmaril.DeBruijn (lift liftN)

variable {Φ : Type v}

private theorem commute_lifts (n : Nat) (σ : Nat → Region Φ) :
    liftLSubstN n (liftLSubstVars σ) = liftLSubstVars (liftLSubstN n σ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [liftLSubstN, liftLSubstN, ih]
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      simp only [liftLSubst, liftLSubstVars, renameVars_renameLabels]

private theorem weaken_block_lsubst (r : Region Φ) (σ : Nat → Region Φ) :
    (r.lsubst (liftLSubstVars σ)).renameVars (lift Nat.succ) =
      (r.renameVars (lift Nat.succ)).lsubst (liftLSubstVars (liftLSubstVars σ)) := by
  rw [renameVars_lsubst]
  congr 1
  funext i
  simp only [liftLSubstVars, renameVars_comp]
  congr 1
  funext j
  cases j with
  | zero => rfl
  | succ k => cases k <;> rfl

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ] {Γ Δ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}

theorem lsubst (h : Step Γ r s L) {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) : Step Γ (r.lsubst σ) (s.lsubst σ) K := by
  cases h with
  | @seq n Γ L S a d blocks R ha hd hb =>
    have lifted : LSubst.ValueFamily Γ (List.ofFn R ++ L) (List.ofFn R ++ K) (liftLSubstN n σ) := by
      simpa only [List.length_ofFn] using hσ.append (List.ofFn R)
    simpa only [Region.lsubst, commute_lifts, weaken_block_lsubst] using
      (Step.seq R ha (hd.lsubst (lifted.liftVars S)) (fun i => (hb i).lsubst (lifted.liftVars (R i))))

omit [HasTy Φ τ] in
private theorem lift_values {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) (B : τ) :
    ∀ ⦃i A⦄, At (B :: Γ) i A → Tm.BranchValue (B :: Δ) (Tm.liftSubst θ i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .var rfl
  | succ i =>
    change Tm.BranchValue (B :: Δ) ((θ i).rename Nat.succ) A
    rw [Tm.rename_eq_subst]
    exact (hθ hi).subst (fun _ _ h => .var (Ren.wk Δ B h))

theorem substVars (h : Step Γ r s L) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    Step Δ (r.substVars θ) (s.substVars θ) L := by
  cases h with
  | @seq n Γ L S a d blocks R ha hd hb =>
    have ha' := ha.subst (fun i A hi => (hθ (i := i) (A := A) hi).hasType)
    simpa only [Region.substVars, substVars_renameVars, renameVars_substVars, Tm.liftSubst_comp_lift_succ] using
      (Step.seq R ha' (hd.substVars (lift_values hθ S))
        (fun i => (hb i).substVars (lift_values hθ (R i))))

theorem renameLabels (h : Step Γ r s L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    Step Γ (r.renameLabels ρ) (s.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst, renameLabels_eq_lsubst]
  exact lsubst h (fun i _ hi => .br (hρ hi) (.var rfl))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplay
