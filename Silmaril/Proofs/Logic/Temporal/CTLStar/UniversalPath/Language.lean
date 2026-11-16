module

public import Silmaril.Logic.Temporal.CTLStar.UniversalPath.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.UniversalPath
open Buchi.Automaton

/-- Closed scalar dual complements truth for every external environment. -/
theorem closed_dual_correct {S : ModalMu.Signature} (q : ModalMu.Formula S 0)
    (M : ModalMu.Model S) (ρ : ModalMu.Env M.World 0) (w : M.World) :
    w ∈ q.dual.denote M ρ ↔ ¬ w ∈ q.denote M ρ := by
  have he : (fun i : Fin 0 => (ρ i)ᶜ) = ρ := funext fun i => i.elim0
  have hd := q.denote_dual M ρ
  rw [he] at hd
  exact Set.ext_iff.mp hd w

/-- Every actual maximal path, finite endpoints and infinite paths included. -/
theorem all_iff {A W : Type} (p : NNF.Formula A) (R : W → W → Prop)
    (label : W → A → Prop) (w : W) :
    AllPaths p R label w ↔ ∀ path : CTLStar.Path R, path.state 0 = w →
      p.Holds path.last (fun t => label (path.state t)) 0 := by
  classical
  simp only [AllPaths, MaximalPath.accepts_iff, not_exists, not_and,
    NNF.Formula.holds_dual, not_not]

/-- The emitted scalar formula forbids exactly the accepting counterexamples. -/
theorem formula_iff_all {S : ModalMu.Signature} (p : NNF.Formula S.Atom)
    (a : S.Action) (M : ModalMu.Model S) (ρ : ModalMu.Env M.World 0) (w : M.World) :
    w ∈ (allFormula p a).denote M ρ ↔ AllPaths p (M.step a) (modelLabel M) w := by
  rw [allFormula, closed_dual_correct, MaximalPath.formula_iff_accepts]
  rfl

/-- Exact universal maximal-path semantics on the original model and worlds. -/
theorem formula_correct {S : ModalMu.Signature} (p : NNF.Formula S.Atom)
    (a : S.Action) (M : ModalMu.Model S) (ρ : ModalMu.Env M.World 0) (w : M.World) :
    w ∈ (allFormula p a).denote M ρ ↔
      ∀ path : CTLStar.Path (M.step a), path.state 0 = w →
        p.Holds path.last (fun t => modelLabel M (path.state t)) 0 := by
  rw [formula_iff_all, all_iff]

/-- Existing actual CTLStar universal-path interpretation of semantic leaves.
The leaves are interpreted, rather than recursively compiled here. -/
theorem all_iff_allPaths {A : Type} {S : CTLStar.Signature}
    (leaf : A → StateFormula S) (M : CTLStar.Model S) (p : NNF.Formula A)
    (w : M.toModal.World) :
    AllPaths p M.toModal.accessible (fun v a => (leaf a).Holds M v) w ↔
      (StateFormula.allPaths (p.toPathFormula leaf)).Holds M w := by
  classical
  rw [all_iff]
  change (∀ path : CTLStar.Path M.toModal.accessible, path.state 0 = w → _) ↔
    ¬ ∃ path : CTLStar.Path M.toModal.accessible,
      path.state 0 = w ∧ ¬ (p.toPathFormula leaf).Holds M path 0
  constructor
  · intro h
    rintro ⟨path, h0, hn⟩
    exact hn ((p.holds_toPathFormula leaf M path 0 path.valid_zero).mp (h path h0))
  · intro h path h0
    apply (p.holds_toPathFormula leaf M path 0 path.valid_zero).mpr
    by_contra hn
    exact h ⟨path, h0, hn⟩

end Silmaril.Logic.Temporal.CTLStar.UniversalPath
