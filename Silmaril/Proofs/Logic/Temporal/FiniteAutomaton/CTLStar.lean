module

public import Silmaril.Logic.Temporal.FiniteAutomaton.Thms
public import Silmaril.Logic.Temporal.CTLStar.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.FiniteAutomaton
open ModalMu Buchi.Automaton

/-- Optional bridge to the existing actual maximal-path representation.
The same run reads exactly the valid positions ending at the stated finite last. -/
theorem pathRun_iff_ctlstarPath {Atom W : Type} {n : Nat} (F : Symbolic Atom n)
    (R : W → W → Prop) (label : W → Atom → Prop) (w : W) (q : Fin n) :
    PathRunFrom F R label w q ↔
      ∃ length : Nat, ∃ path : CTLStar.Path R, ∃ run : Nat → Fin n,
        path.last = some length ∧ path.state 0 = w ∧ run 0 = q ∧
        (∀ i, i < length → (F.guard (run i) (run (i+1))).Holds (label (path.state i))) ∧
        (F.terminal (run length)).Holds (label (path.state length)) := by
  constructor
  · rintro ⟨length, path, run, h0, r0, edges, ht, hd⟩
    let actual : CTLStar.Path R := {
      state := path
      last := some length
      edges := fun i hi => (edges i (by change i+1 ≤ length at hi; omega)).1
      terminal := by
        intro k hk
        have h : length = k := Option.some.inj hk
        subst k
        exact hd }
    exact ⟨length, actual, run, rfl, h0, r0, fun i hi => (edges i hi).2, ht⟩
  · rintro ⟨length, path, run, hl, h0, r0, guards, ht⟩
    refine ⟨length, path.state, run, h0, r0, ?_, ht, path.terminal length hl⟩
    intro i hi
    refine ⟨path.edges i ?_, guards i hi⟩
    rw [hl]
    change i+1 ≤ length
    omega

end Silmaril.Logic.Temporal.FiniteAutomaton
