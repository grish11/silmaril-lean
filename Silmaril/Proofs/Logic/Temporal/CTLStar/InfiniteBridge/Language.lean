module

public import Silmaril.Logic.Temporal.CTLStar.InfiniteBridge.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.NNF

/-- Exact infinite-word meaning at every index; the erasure requires last=none. -/
theorem Formula.holds_toInfinite {A : Type} (p : Formula A)
    (word : Nat → A → Prop) (i : Nat) :
    p.toInfinite.Holds word i ↔ p.Holds none word i := by
  induction p generalizing i <;>
    simp_all [toInfinite, Holds, LTL.NNF.Formula.Holds, ValidIndex]

end Silmaril.Logic.Temporal.CTLStar.NNF

noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.InfiniteBridge
open Buchi.Automaton

/-- The existing Büchi recurrence rejects indefinitely postponed Until. -/
theorem accepts_iff {A : Type} (p : NNF.Formula A) (word : Nat → A → Prop) :
    (automaton p).Accepts word ↔ p.Holds none word 0 :=
  (LTL.Tableau.accepts_iff p.toInfinite word).trans (p.holds_toInfinite word 0)

/-- One coherent infinite original graph path and its actual label word. -/
theorem accepts_path_iff {A W : Type} (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → A → Prop) (w : W) :
    (automaton p).AcceptsPath R label w ↔
      ∃ path : Nat → W, IsPath R w path ∧ p.Holds none (fun t => label (path t)) 0 := by
  simp only [Generalized.Symbolic.AcceptsPath, accepts_iff, Function.comp_def]

/-- The actual scalar adapter preserves the original worlds, edge relation
and one shared path through every temporal and Boolean constraint. -/
theorem formula_correct {S : ModalMu.Signature} (p : NNF.Formula S.Atom)
    (a : S.Action) (M : ModalMu.Model S) (ρ : ModalMu.Env M.World 0) (w : M.World) :
    w ∈ (formula p a).denote M ρ ↔ ∃ path : Nat → M.World,
      IsPath (M.step a) w path ∧ p.Holds none (fun t => modelLabel M (path t)) 0 := by
  rw [formula, LTL.Tableau.formula_correct]
  exact exists_congr fun path => and_congr_right fun _ => p.holds_toInfinite _ 0

/-- Existing actual CTLStar paths, with no finite endpoint. No seriality
assumption is imposed on the rest of the graph. -/
theorem accepts_iff_ctlstarPath {A W : Type} (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → A → Prop) (w : W) :
    (automaton p).AcceptsPath R label w ↔
      ∃ path : CTLStar.Path R, path.last = none ∧ path.state 0 = w ∧
        p.Holds path.last (fun t => label (path.state t)) 0 := by
  rw [accepts_path_iff]
  constructor
  · rintro ⟨path, ⟨h0, edges⟩, hp⟩
    let actual : CTLStar.Path R := {
      state := path
      last := none
      edges := fun i _ => edges i
      terminal := by intro n hn; cases hn }
    exact ⟨actual, rfl, h0, hp⟩
  · rintro ⟨path, hl, h0, hp⟩
    refine ⟨path.state, ⟨h0, ?_⟩, ?_⟩
    · intro i
      exact path.edges i (by simp only [hl, ValidIndex])
    · simpa only [hl] using hp

/-- Actual CTLStar satisfaction on any specified infinite maximal path. -/
theorem accepts_pathFormula_iff {A : Type} {S : CTLStar.Signature}
    (leaf : A → StateFormula S) (M : CTLStar.Model S)
    (path : CTLStar.Path M.toModal.accessible) (p : NNF.Formula A)
    (hlast : path.last = none) :
    (automaton p).Accepts (fun t a => (leaf a).Holds M (path.state t)) ↔
      (p.toPathFormula leaf).Holds M path 0 := by
  rw [accepts_iff, ← hlast]
  exact p.holds_toPathFormula leaf M path 0 path.valid_zero

/-- Both normalization polarities, with nested state formulas retained as
interpreted leaves; this does not recursively compile those leaves. -/
theorem accepts_normalize_iff {S : CTLStar.Signature} (M : CTLStar.Model S)
    (path : CTLStar.Path M.toModal.accessible) (p : PathFormula S) (b : Bool)
    (hlast : path.last = none) :
    (automaton (NNF.normalize b p)).Accepts (fun t a => a.Holds M (path.state t)) ↔
      if b then ¬ p.Holds M path 0 else p.Holds M path 0 := by
  rw [accepts_iff, ← hlast]
  exact NNF.normalize_holds M path p b 0 path.valid_zero

/-- Scalar semantics packaged as actual original-frame infinite CTLStar paths. -/
theorem formula_iff_ctlstarPath {S : ModalMu.Signature} (p : NNF.Formula S.Atom)
    (a : S.Action) (M : ModalMu.Model S) (ρ : ModalMu.Env M.World 0) (w : M.World) :
    w ∈ (formula p a).denote M ρ ↔
      ∃ path : CTLStar.Path (M.step a), path.last = none ∧ path.state 0 = w ∧
        p.Holds path.last (fun t => modelLabel M (path.state t)) 0 := by
  rw [formula, LTL.Tableau.formula, Buchi.Automaton.Generalized.formula_correct]
  exact accepts_iff_ctlstarPath p _ _ w

end Silmaril.Logic.Temporal.CTLStar.InfiniteBridge
