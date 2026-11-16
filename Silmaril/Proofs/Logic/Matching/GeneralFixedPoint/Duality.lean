module

public import Silmaril.Proofs.Logic.Matching.GeneralFixedPoint.Variance
public import Silmaril.Logic.ModalMu.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

/-- Complement both the argument and result of a monotone set function. -/
def complementConjugate {W : Type} (F : Set W →o Set W) : Set W →o Set W where
  toFun X := (F Xᶜ)ᶜ
  monotone' := fun _ _ h =>
    Set.compl_subset_compl.mpr (F.monotone (Set.compl_subset_compl.mpr h))

/-- The direct ν semantics agrees with the paper's complemented μ construction.
This is the semantic conjugation law; no new substitution syntax is assumed. -/
theorem nu_complement_mu (M : Model A) {r k : Nat} {P : Fin (r+1) → S}
    {Γ : Fin k → S} (p : Pattern A P Γ (P 0))
    (positive : p.occurs true 0 = false) (v : ObjEnv A M Γ)
    (η : SetEnv A M (P ∘ Fin.succ)) :
    (Pattern.nu p).denote M v η =
      ((complementConjugate (p.bodyOrderHom M positive v η)).lfp)ᶜ := by
  have h := ModalMu.lfp_complement_gfp (p.bodyOrderHom M positive v η)
    (complementConjugate (p.bodyOrderHom M positive v η)) (fun _ => rfl)
  have hc := congrArg (fun X : Set (M.carrier (P 0)) => Xᶜ) h
  change (p.bodyOrderHom M positive v η).gfp = _
  simpa only [compl_compl] using hc.symm
end Silmaril.Logic.Matching.GeneralFixedPoint
