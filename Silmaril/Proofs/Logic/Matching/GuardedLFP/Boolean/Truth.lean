module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Boolean.Quantifiers

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP.Boolean
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

theorem restrictEnv_flip (M : Model S) {r : Nat} {P : Fin r → Profile S}
    (σ : Fin r → Bool)
    (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P)) :
    restrictEnv M (fun i => !(σ i)) (fun i => (η i)ᶜ) = restrictEnv M σ η := by
  classical
  funext i
  apply Set.ext
  intro x
  cases hs : σ i
  · simp only [restrictEnv, hs, Bool.not_false, Bool.false_eq_true, ite_true, ite_false]
    rfl
  · simp only [restrictEnv, hs, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
    change (¬¬ tupleEncode M (P i) x ∈ η i) ↔ tupleEncode M (P i) x ∈ η i
    exact not_not

/-- Every admitted native model, arbitrary raw set environment and active object
assignment satisfies the complete signed Boolean syntax, including negated LFPs.
Negative free variables use the declared complement convention explicitly. -/
theorem formula_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} {σ : Fin r → Bool} (p : FirstOrderLFP.Boolean.Formula S P Γ σ) :
    ∀ (v : FirstOrderLFP.ObjEnv (decode M) Γ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula p).denote M.base (fun i => (v i).val) η ↔
        v ∈ p.denote (decode M) (restrictEnv M σ η) := by
  induction p with
  | base p =>
      intro v η w
      exact (Iff.of_eq (congrArg (fun X => w ∈ X)
        (SortMaps.Hom.denote_pattern (baseSignature S) M.base (GuardedFOL.formula p) _))).trans
          (GuardedFOL.formula_denote (guardedModel M) p v w)
  | @pred r k P Γ σ i positive args =>
      intro v η w
      have h := GuardedLFP.pred_denote M i args v η w
      change w ∈ (tupleDefined (.conj (packTerms args) (.setvar i))).denote M.base _ η ↔
        (fun j => (args j).eval (decode M).toStructure.toAlgebra v) ∈ GuardedLFP.restrictEnv M η i at h
      change w ∈ (tupleDefined (.conj (packTerms args) (.setvar i))).denote M.base _ η ↔
        (fun j => (args j).eval (decode M).toStructure.toAlgebra v) ∈ restrictEnv M σ η i
      simpa only [restrictEnv, positive, ite_true] using h
  | @neg r k P Γ σ p ih =>
      intro v η w
      have hη : (fun i => ((η i)ᶜ)ᶜ) = η := funext fun _ => compl_compl _
      have hd := FixedPoint.Pattern.denote_dual M.base (formula p) (fun i => (v i).val)
        (fun i => (η i)ᶜ)
      rw [hη] at hd
      change w ∈ (formula p).dual.denote M.base (fun i => (v i).val) η ↔
        v ∉ p.denote (decode M) (restrictEnv M σ η)
      rw [hd]
      have h := ih v (fun i => (η i)ᶜ) w
      rw [restrictEnv_flip] at h
      exact not_congr h
  | conj p q hp hq =>
      intro v η w
      exact and_congr (hp v η w) (hq v η w)
  | disj p q hp hq =>
      intro v η w
      exact or_congr (hp v η w) (hq v η w)
  | all p hp => exact all_denote M p hp
  | ex p hp => exact ex_denote M p hp
  | lfp ht hp body args ih => exact lfp_denote M ht hp body args ih

end Silmaril.Logic.Matching.GuardedLFP.Boolean
