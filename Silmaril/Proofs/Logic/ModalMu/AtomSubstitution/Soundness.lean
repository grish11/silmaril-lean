module

public import Silmaril.Logic.ModalMu.AtomSubstitution.Defs

@[expose] public section
namespace Silmaril.Logic.ModalMu
open CategoryTheory

/-- The closed dual complements truth independently of an external environment. -/
theorem Formula.denote_closed_dual {S : Signature} (M : Model S) (p : Formula S 0) :
    p.dual.denote M emptyEnv = (p.denote M emptyEnv)ᶜ := by
  have he : (fun i : Fin 0 => (emptyEnv i : Set M.World)ᶜ) = emptyEnv := by
    funext i
    exact i.elim0
  simpa only [he] using p.denote_dual M emptyEnv

/-- Atom replacement preserves the entire monotone map of free-variable environments. -/
theorem Formula.denote_replaceAtoms {S T : Signature} (act : S.Action → T.Action)
    (σ : S.Atom → Formula T 0) (M : Model T) {n : Nat} (p : Formula S n) :
    (p.replaceAtoms act σ).denote M = p.denote (atomReduct act σ M) := by
  apply OrderHom.ext
  funext ρ
  induction p with
  | pos a => exact (σ a).denote_closedAt M _ ρ
  | neg a =>
      change ((σ a).dual.closedAt _).denote M ρ = ((σ a).denote M emptyEnv)ᶜ
      rw [Formula.denote_closedAt, Formula.denote_closed_dual]
  | bot => rfl
  | top => rfl
  | var i => rfl
  | conj p q hp hq =>
      change (p.replaceAtoms act σ).denote M ρ ∩ (q.replaceAtoms act σ).denote M ρ =
        p.denote (atomReduct act σ M) ρ ∩ q.denote (atomReduct act σ M) ρ
      rw [hp, hq]
      rfl
  | disj p q hp hq =>
      change (p.replaceAtoms act σ).denote M ρ ∪ (q.replaceAtoms act σ).denote M ρ =
        p.denote (atomReduct act σ M) ρ ∪ q.denote (atomReduct act σ M) ρ
      rw [hp, hq]
      rfl
  | box a p hp =>
      change {w | ∀ v, M.step (act a) w v → v ∈ (p.replaceAtoms act σ).denote M ρ} =
        {w | ∀ v, M.step (act a) w v → v ∈ p.denote (atomReduct act σ M) ρ}
      rw [hp]
      rfl
  | diamond a p hp =>
      change {w | ∃ v, M.step (act a) w v ∧ v ∈ (p.replaceAtoms act σ).denote M ρ} =
        {w | ∃ v, M.step (act a) w v ∧ v ∈ p.denote (atomReduct act σ M) ρ}
      rw [hp]
      rfl
  | mu p hp =>
      change ((p.replaceAtoms act σ).denote M |>.comp (insert ρ)).lfp =
        ((p.denote (atomReduct act σ M)).comp (insert ρ)).lfp
      congr 1
      apply OrderHom.ext
      funext X
      exact hp (extend ρ X)
  | nu p hp =>
      change ((p.replaceAtoms act σ).denote M |>.comp (insert ρ)).gfp =
        ((p.denote (atomReduct act σ M)).comp (insert ρ)).gfp
      congr 1
      apply OrderHom.ext
      funext X
      exact hp (extend ρ X)

theorem sat_replaceAtoms {S T : Signature} (act : S.Action → T.Action)
    (σ : S.Atom → Formula T 0) (M : Model T) (p : Formula S 0) :
    Sat M (p.replaceAtoms act σ) ↔ Sat (atomReduct act σ M) p := by
  unfold Sat
  rw [Formula.denote_replaceAtoms]
  rfl

/-- Target signature renaming acts on the actual replacements and modal actions. -/
theorem Formula.replaceAtoms_map {S T U : Signature} (act : S.Action → T.Action)
    (σ : S.Atom → Formula T 0) (f : T ⟶ U) {n : Nat} (p : Formula S n) :
    (p.replaceAtoms act σ).map f =
      p.replaceAtoms (f.action ∘ act) (fun a => (σ a).map f) := by
  induction p <;> simp_all [Formula.replaceAtoms, Formula.map, Formula.closedAt,
    ← Formula.renameVars_map, ← Formula.dual_map]

/-- Source signature renaming precomposes the actual replacement family.
The target replacements stay closed and free fixed-point variables are preserved. -/
theorem Formula.map_replaceAtoms {S T U : Signature} (f : S ⟶ T)
    (act : T.Action → U.Action) (σ : T.Atom → Formula U 0) {n : Nat}
    (p : Formula S n) :
    (p.map f).replaceAtoms act σ =
      p.replaceAtoms (act ∘ f.action) (fun a => σ (f.atom a)) := by
  induction p <;> simp_all [Formula.map, Formula.replaceAtoms]

end Silmaril.Logic.ModalMu
