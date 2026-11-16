module

public import Silmaril.Logic.ModalMu.Substitution.Defs

@[expose] public section
namespace Silmaril.Logic.ModalMu
open CategoryTheory

theorem Formula.denote_substitute {S : Signature} (M : Model S) {n : Nat} (p : Formula S n) :
    ∀ {m : Nat} (σ : Fin n → Formula S m) (ρ : Env M.World m),
    (p.substitute σ).denote M ρ = p.denote M (fun i => (σ i).denote M ρ) := by
  induction p with
  | pos a => intros; rfl
  | neg a => intros; rfl
  | bot => intros; rfl
  | top => intros; rfl
  | var i => intros; rfl
  | conj p q hp hq =>
      intro m σ ρ
      change (p.substitute σ).denote M ρ ∩ (q.substitute σ).denote M ρ = _
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      intro m σ ρ
      change (p.substitute σ).denote M ρ ∪ (q.substitute σ).denote M ρ = _
      rw [hp, hq]
      rfl
  | box a p hp =>
      intro m σ ρ
      change {w | ∀ v, M.step a w v → v ∈ (p.substitute σ).denote M ρ} = _
      rw [hp]
      rfl
  | diamond a p hp =>
      intro m σ ρ
      change {w | ∃ v, M.step a w v ∧ v ∈ (p.substitute σ).denote M ρ} = _
      rw [hp]
      rfl
  | mu p hp =>
      intro m σ ρ
      change ((p.substitute (liftSubstitution σ)).denote M |>.comp (insert ρ)).lfp =
        ((p.denote M).comp (insert (fun i => (σ i).denote M ρ))).lfp
      congr 1
      apply OrderHom.ext
      funext X
      change (p.substitute (liftSubstitution σ)).denote M (extend ρ X) = _
      rw [hp]
      apply congrArg (fun η => p.denote M η)
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact (σ j).denote_shift M ρ X
  | nu p hp =>
      intro m σ ρ
      change ((p.substitute (liftSubstitution σ)).denote M |>.comp (insert ρ)).gfp =
        ((p.denote M).comp (insert (fun i => (σ i).denote M ρ))).gfp
      congr 1
      apply OrderHom.ext
      funext X
      change (p.substitute (liftSubstitution σ)).denote M (extend ρ X) = _
      rw [hp]
      apply congrArg (fun η => p.denote M η)
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact (σ j).denote_shift M ρ X

theorem liftSubstitution_map {S T : Signature} (f : S ⟶ T) {n m : Nat}
    (σ : Fin n → Formula S m) :
    (fun i => (liftSubstitution σ i).map f) = liftSubstitution (fun i => (σ i).map f) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact ((σ j).renameVars_map f Fin.succ).symm

/-- Arbitrary atom/action maps commute with actual capture-safe substitution. -/
theorem Formula.substitute_map {S T : Signature} (f : S ⟶ T) {n : Nat} (p : Formula S n) :
    ∀ {m : Nat} (σ : Fin n → Formula S m),
    (p.substitute σ).map f = (p.map f).substitute (fun i => (σ i).map f) := by
  induction p <;> intros <;>
    simp_all only [Formula.substitute, Formula.map, liftSubstitution_map]

end Silmaril.Logic.ModalMu
