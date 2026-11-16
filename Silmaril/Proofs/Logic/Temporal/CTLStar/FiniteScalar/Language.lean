module

public import Silmaril.Logic.Temporal.CTLStar.FiniteScalar.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Temporal.CTLStar.FiniteScalar
open LTL.Tableau Buchi.Automaton ModalMu

/-- An individual packed run decodes along the identical bounded path. -/
theorem pathRun_iff {A W : Type} (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → A → Prop) (w : W)
    (q : Fin (Fintype.card (State (FiniteTableau.shape p)))) :
    FiniteAutomaton.PathRunFrom (automaton p) R label w q ↔
      ∃ n, ∃ path : Nat → W, ∃ run : Nat → State (FiniteTableau.shape p),
        path 0 = w ∧ run 0 = (stateEquiv (FiniteTableau.shape p)).symm q ∧
        (∀ i, i < n → R (path i) (path (i+1)) ∧
          (FiniteTableau.transition p (run i) (run (i+1))).Holds (label (path i))) ∧
        (FiniteTableau.terminal p (run n)).Holds (label (path n)) ∧
        (∀ v, ¬ R (path n) v) := by
  constructor
  · rintro ⟨n, path, run, h0, r0, steps, ht, hd⟩
    refine ⟨n, path, (fun t => (stateEquiv _).symm (run t)), h0, ?_, steps, ht, hd⟩
    exact congrArg (stateEquiv (FiniteTableau.shape p)).symm r0
  · rintro ⟨n, path, run, h0, r0, steps, ht, hd⟩
    refine ⟨n, path, (fun t => stateEquiv _ (run t)), h0, ?_, ?_, ?_, hd⟩
    · simp only [r0, Equiv.apply_symm_apply]
    · intro i hi
      simpa only [automaton, pack, Equiv.symm_apply_apply] using steps i hi
    · simpa only [automaton, pack, Equiv.symm_apply_apply] using ht

/-- Packing changes only the assignment representation. Length, path, labels
and terminal deadlock stay exactly the same. -/
theorem accepts_iff_tableau {A W : Type} (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → A → Prop) (w : W) :
    FiniteAutomaton.AcceptsPath (automaton p) R label w ↔
      ∃ n, ∃ path : Nat → W, path 0 = w ∧
        (∀ i, i < n → R (path i) (path (i+1))) ∧
        (∀ v, ¬ R (path n) v) ∧
        FiniteTableau.Accepts p n (fun t => label (path t)) := by
  constructor
  · rintro ⟨q, hi, n, path, run, h0, r0, edges, ht, hd⟩
    refine ⟨n, path, h0, fun i h => (edges i h).1, hd,
      (fun t => (stateEquiv (FiniteTableau.shape p)).symm (run t)), ?_,
      (fun i h => (edges i h).2), ht⟩
    change bit ((stateEquiv (FiniteTableau.shape p)).symm q) = true at hi
    simpa only [r0] using hi
  · rintro ⟨n, path, h0, edges, hd, run, hi, steps, ht⟩
    refine ⟨stateEquiv (FiniteTableau.shape p) (run 0), ?_, n, path,
      (fun t => stateEquiv (FiniteTableau.shape p) (run t)), h0, rfl, ?_, ?_, hd⟩
    · change bit ((stateEquiv _).symm (stateEquiv _ (run 0))) = true
      simpa only [Equiv.symm_apply_apply] using hi
    · intro i h
      refine ⟨edges i h, ?_⟩
      change (FiniteTableau.transition p ((stateEquiv _).symm (stateEquiv _ (run i)))
        ((stateEquiv _).symm (stateEquiv _ (run (i+1))))).Holds (label (path i))
      simpa only [Equiv.symm_apply_apply] using steps i h
    · change (FiniteTableau.terminal p ((stateEquiv _).symm (stateEquiv _ (run n)))).Holds _
      simpa only [Equiv.symm_apply_apply] using ht

/-- Exact finite maximal original-path language, including zero edges. -/
theorem accepts_iff {A W : Type} (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → A → Prop) (w : W) :
    FiniteAutomaton.AcceptsPath (automaton p) R label w ↔
      ∃ n, ∃ path : Nat → W, path 0 = w ∧
        (∀ i, i < n → R (path i) (path (i+1))) ∧
        (∀ v, ¬ R (path n) v) ∧ p.Holds (some n) (fun t => label (path t)) 0 := by
  simp only [accepts_iff_tableau, FiniteTableau.accepts_iff]

/-- The emitted scalar formula holds precisely on one coherent original path. -/
theorem formula_correct {S : ModalMu.Signature} (p : NNF.Formula S.Atom) (a : S.Action)
    (M : ModalMu.Model S) (ρ : Env M.World 0) (w : M.World) :
    w ∈ (formula p a).denote M ρ ↔
      ∃ n, ∃ path : Nat → M.World, path 0 = w ∧
        (∀ i, i < n → M.step a (path i) (path (i+1))) ∧
        (∀ v, ¬ M.step a (path n) v) ∧
        p.Holds (some n) (fun t => modelLabel M (path t)) 0 := by
  rw [formula, FiniteAutomaton.formula_correct, accepts_iff]

/-- Actual existing CTLStar maximal paths, with the same finite endpoint. -/
theorem accepts_iff_ctlstarPath {A W : Type} (p : NNF.Formula A)
    (R : W → W → Prop) (label : W → A → Prop) (w : W) :
    FiniteAutomaton.AcceptsPath (automaton p) R label w ↔
      ∃ n, ∃ path : CTLStar.Path R, path.last = some n ∧ path.state 0 = w ∧
        p.Holds path.last (fun t => label (path.state t)) 0 := by
  rw [accepts_iff]
  constructor
  · rintro ⟨n, path, h0, edges, hd, hp⟩
    let actual : CTLStar.Path R := {
      state := path
      last := some n
      edges := fun i hi => edges i (by change i+1 ≤ n at hi; omega)
      terminal := by intro k hk; cases Option.some.inj hk; exact hd }
    exact ⟨n, actual, rfl, h0, hp⟩
  · rintro ⟨n, path, hl, h0, hp⟩
    refine ⟨n, path.state, h0, ?_, path.terminal n hl, ?_⟩
    · intro i hi
      apply path.edges i
      rw [hl]
      change i+1 ≤ n
      omega
    · simpa only [hl] using hp

/-- Existing CTLStar satisfaction, with ordinary state leaves interpreted on
an actual finite maximal path of its original model. -/
theorem accepts_iff_pathFormula {A : Type} {S : CTLStar.Signature}
    (leaf : A → StateFormula S) (M : CTLStar.Model S) (p : NNF.Formula A)
    (w : M.toModal.World) :
    FiniteAutomaton.AcceptsPath (automaton p) M.toModal.accessible
      (fun v a => (leaf a).Holds M v) w ↔
      ∃ n, ∃ path : CTLStar.Path M.toModal.accessible,
        path.last = some n ∧ path.state 0 = w ∧ (p.toPathFormula leaf).Holds M path 0 := by
  rw [accepts_iff_ctlstarPath]
  apply exists_congr
  intro n
  apply exists_congr
  intro path
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact p.holds_toPathFormula leaf M path 0 path.valid_zero

end Silmaril.Logic.Temporal.CTLStar.FiniteScalar
