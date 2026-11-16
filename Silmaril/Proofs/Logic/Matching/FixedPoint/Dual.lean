module

public import Silmaril.Logic.Matching.FixedPoint.Thms
public import Silmaril.Logic.ModalMu.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint
open Algebraic.ManySorted (Signature)
variable {S : Type} {A : Signature S}

/-- De Morgan dual complements every free set-variable valuation. -/
def Pattern.dual {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : Pattern A P Γ s) : Pattern A P Γ s := by
  induction p with
  | base p => exact .base (.neg p)
  | setvar i => exact .setvar i
  | app op args ih => exact .dualApp op ih
  | dualApp op args ih => exact .app op ih
  | conj p q hp hq => exact .disj hp hq
  | disj p q hp hq => exact .conj hp hq
  | ex bound p hp => exact .all bound hp
  | all bound p hp => exact .ex bound hp
  | mu p hp => exact .nu hp
  | nu p hp => exact .mu hp

theorem Pattern.denote_dual (M : Model A) {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) :
    ∀ (v : ObjEnv A M Γ) (η : SetEnv A M P),
      p.dual.denote M v (fun i => (η i)ᶜ) = (p.denote M v η)ᶜ := by
  classical
  induction p with
  | base => intro v η; rfl
  | setvar => intro v η; rfl
  | app op args ih =>
      intro v η
      change (application M op (fun i => ((args i).dual.denote M v (fun j => (η j)ᶜ))ᶜ))ᶜ = _
      simp only [ih, compl_compl]
      rfl
  | dualApp op args ih =>
      intro v η
      change application M op (fun i => (args i).dual.denote M v (fun j => (η j)ᶜ)) = _
      simp only [ih]
      exact (compl_compl (application M op (fun i => ((args i).denote M v η)ᶜ))).symm
  | conj p q hp hq =>
      intro v η
      change p.dual.denote M v _ ∪ q.dual.denote M v _ = _
      rw [hp, hq]
      exact (Set.compl_inter _ _).symm
  | disj p q hp hq =>
      intro v η
      change p.dual.denote M v _ ∩ q.dual.denote M v _ = _
      rw [hp, hq]
      exact (Set.compl_union _ _).symm
  | ex bound p hp =>
      show ∀ v η, (Pattern.ex bound p).dual.denote M v (fun i => (η i)ᶜ) =
        ((Pattern.ex bound p).denote M v η)ᶜ
      intro v η
      change {x | ∀ a : M.carrier bound, x ∈ p.dual.denote M (Fin.cases a v) _} = _
      simp only [hp]
      apply Set.ext
      intro x
      change (∀ a : M.carrier bound, x ∉ p.denote M (Fin.cases a v) η) ↔
        ¬ ∃ a : M.carrier bound, x ∈ p.denote M (Fin.cases a v) η
      exact not_exists.symm
  | all bound p hp =>
      show ∀ v η, (Pattern.all bound p).dual.denote M v (fun i => (η i)ᶜ) =
        ((Pattern.all bound p).denote M v η)ᶜ
      intro v η
      change {x | ∃ a : M.carrier bound, x ∈ p.dual.denote M (Fin.cases a v) _} = _
      simp only [hp]
      apply Set.ext
      intro x
      change (∃ a : M.carrier bound, x ∉ p.denote M (Fin.cases a v) η) ↔
        ¬ ∀ a : M.carrier bound, x ∈ p.denote M (Fin.cases a v) η
      exact not_forall.symm
  | @mu r k P' Γ p hp =>
      show ∀ v η, (Pattern.mu p).dual.denote M v (fun i => (η i)ᶜ) =
        ((Pattern.mu p).denote M v η)ᶜ
      intro v η
      apply ModalMu.gfp_complement_lfp
      intro X
      change p.dual.denote M v (Fin.cases X (fun i => (η i)ᶜ)) =
        (p.denote M v (Fin.cases Xᶜ η))ᶜ
      have he : (Fin.cases X (fun i => (η i)ᶜ) : SetEnv A M P') =
          fun i => ((Fin.cases Xᶜ η : SetEnv A M P') i)ᶜ := by
        funext i
        exact Fin.cases (compl_compl X).symm (fun _ => rfl) i
      rw [he]
      exact hp v _
  | @nu r k P' Γ p hp =>
      show ∀ v η, (Pattern.nu p).dual.denote M v (fun i => (η i)ᶜ) =
        ((Pattern.nu p).denote M v η)ᶜ
      intro v η
      apply ModalMu.lfp_complement_gfp
      intro X
      change p.dual.denote M v (Fin.cases X (fun i => (η i)ᶜ)) =
        (p.denote M v (Fin.cases Xᶜ η))ᶜ
      have he : (Fin.cases X (fun i => (η i)ᶜ) : SetEnv A M P') =
          fun i => ((Fin.cases Xᶜ η : SetEnv A M P') i)ᶜ := by
        funext i
        exact Fin.cases (compl_compl X).symm (fun _ => rfl) i
      rw [he]
      exact hp v _

end Silmaril.Logic.Matching.FixedPoint
