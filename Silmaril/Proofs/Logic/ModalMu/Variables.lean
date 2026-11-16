module

public import Silmaril.Logic.ModalMu.Variables.Defs

@[expose] public section
namespace Silmaril.Logic.ModalMu
open CategoryTheory

/-- Capture-free renaming reindexes precisely the semantic environment. -/
theorem Formula.denote_renameVars {S : Signature} (M : Model S) {n : Nat} (p : Formula S n) :
    ∀ {m : Nat} (f : Fin n → Fin m) (ρ : Env M.World m),
      (p.renameVars f).denote M ρ = p.denote M (fun i => ρ (f i)) := by
  induction p with
  | pos a => intros; rfl
  | neg a => intros; rfl
  | bot => intros; rfl
  | top => intros; rfl
  | var i => intros; rfl
  | conj p q hp hq =>
      intro m f ρ
      change (p.renameVars f).denote M ρ ∩ (q.renameVars f).denote M ρ =
        p.denote M _ ∩ q.denote M _
      rw [hp, hq]
  | disj p q hp hq =>
      intro m f ρ
      change (p.renameVars f).denote M ρ ∪ (q.renameVars f).denote M ρ =
        p.denote M _ ∪ q.denote M _
      rw [hp, hq]
  | box a p hp =>
      intro m f ρ
      change {w | ∀ v, M.step a w v → v ∈ (p.renameVars f).denote M ρ} =
        {w | ∀ v, M.step a w v → v ∈ p.denote M _}
      rw [hp]
  | diamond a p hp =>
      intro m f ρ
      change {w | ∃ v, M.step a w v ∧ v ∈ (p.renameVars f).denote M ρ} =
        {w | ∃ v, M.step a w v ∧ v ∈ p.denote M _}
      rw [hp]
  | mu p hp =>
      show ∀ {m : Nat} (f : _ → Fin m) (ρ : Env M.World m),
        ((Formula.mu p).renameVars f).denote M ρ = (Formula.mu p).denote M (fun i => ρ (f i))
      intro m f ρ
      change ((p.renameVars (liftVars f)).denote M |>.comp (insert ρ)).lfp =
        ((p.denote M).comp (insert (fun i => ρ (f i)))).lfp
      congr 1
      apply OrderHom.ext
      funext X
      change (p.renameVars (liftVars f)).denote M (extend ρ X) = _
      rw [hp]
      apply congrArg (fun η => p.denote M η)
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
  | nu p hp =>
      show ∀ {m : Nat} (f : _ → Fin m) (ρ : Env M.World m),
        ((Formula.nu p).renameVars f).denote M ρ = (Formula.nu p).denote M (fun i => ρ (f i))
      intro m f ρ
      change ((p.renameVars (liftVars f)).denote M |>.comp (insert ρ)).gfp =
        ((p.denote M).comp (insert (fun i => ρ (f i)))).gfp
      congr 1
      apply OrderHom.ext
      funext X
      change (p.renameVars (liftVars f)).denote M (extend ρ X) = _
      rw [hp]
      apply congrArg (fun η => p.denote M η)
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

theorem Formula.denote_shift {S : Signature} (M : Model S) {n : Nat}
    (p : Formula S n) (ρ : Env M.World n) (X : Set M.World) :
    p.shift.denote M (extend ρ X) = p.denote M ρ := p.denote_renameVars M _ _

theorem Formula.denote_closedAt {S : Signature} (M : Model S)
    (p : Formula S 0) (n : Nat) (ρ : Env M.World n) :
    (p.closedAt n).denote M ρ = p.denote M emptyEnv := by
  rw [Formula.closedAt, Formula.denote_renameVars]
  congr 1
  funext i
  exact i.elim0

theorem Formula.renameVars_map {S T : Signature} (f : S ⟶ T) {n : Nat} (p : Formula S n) :
    ∀ {m : Nat} (g : Fin n → Fin m),
    (p.map f).renameVars g = (p.renameVars g).map f := by
  induction p <;> intros <;> simp_all [Formula.map, Formula.renameVars]

theorem Formula.dual_map {S T : Signature} (f : S ⟶ T) {n : Nat} (p : Formula S n) :
    (p.map f).dual = p.dual.map f := by
  induction p <;> simp_all [Formula.map, Formula.dual]

end Silmaril.Logic.ModalMu
