module

public import Silmaril.Proofs.Logic.Matching.GuardedLFP.Quantifiers

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GuardedLFP
open Silmaril.Logic.Institution.Examples
variable {S : FOL.Signature}

/-- Every admitted native model, every active object assignment, every raw set
environment, and every truth element satisfy the full positive source semantics. -/
theorem formula_denote (M : Model S) {r k : Nat} {P : Fin r → Profile S}
    {Γ : Fin k → S.S} (p : FirstOrderLFP.Formula S P Γ) :
    ∀ (v : FirstOrderLFP.ObjEnv (decode M) Γ)
      (η : FixedPoint.SetEnv (signature S).symbols M.base (setContext P))
      (w : M.base.carrier (.base .truth)),
      w ∈ (formula p).denote M.base (fun i => (v i).val) η ↔
        v ∈ p.denote (decode M) (restrictEnv M η) := by
  induction p with
  | base p =>
      intro v η w
      exact (Iff.of_eq (congrArg (fun X => w ∈ X)
        (SortMaps.Hom.denote_pattern (baseSignature S) M.base (GuardedFOL.formula p) _))).trans
          (GuardedFOL.formula_denote (guardedModel M) p v w)
  | pred i args => exact pred_denote M i args
  | conj p q hp hq =>
      intro v η w
      exact and_congr (hp v η w) (hq v η w)
  | disj p q hp hq =>
      intro v η w
      exact or_congr (hp v η w) (hq v η w)
  | all p hp => exact all_denote M p hp
  | ex p hp => exact ex_denote M p hp
  | lfp ht hp body args ih => exact lfp_denote M ht hp body args ih
end Silmaril.Logic.Matching.GuardedLFP
