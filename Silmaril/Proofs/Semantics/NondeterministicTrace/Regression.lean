module

import Silmaril.Semantics.NondeterministicTrace.Thms

namespace Silmaril.Proofs.Semantics.NondeterministicTrace.Regression

open Silmaril.Elgot
open Silmaril.Semantics.NondeterministicTrace

variable {W : Type} [Monoid W]

private def repeatBody (w : W) (a : Unit) : Finite W (Unit ⊕ Unit) :=
  Finite.ofOutcomes {(.inr a, w)}

/-- Each step emits the given log and recurs. It has no finite return. -/
private theorem repeat_empty (w : W) : (iter (repeatBody w) ()).outcomes = ∅ := by
  have noRun {a b : Unit} {v : W} (run : Finite.Runs (repeatBody w) a b v) : False := by
    induction run with
    | done edge => simp [repeatBody] at edge
    | more _ _ ih => exact ih
  apply Set.eq_empty_iff_forall_notMem.2
  rintro ⟨b, v⟩ obs
  exact noRun ((Finite.mem_iter _ _ _ _).1 obs)

/-- An uninstrumented silent loop supplies no observation. A supplied incomplete
branch with empty log is an observable alternative. -/
example :
    Tagged.outcomes (iter (fun a => Tagged.includeResults (repeatBody (1 : W) a)) () :
      Tagged W Unit Unit) = ∅ ∧
    (.error (), 1) ∈ Tagged.outcomes (Tagged.incomplete () 1 : Tagged W Unit Unit) := by
  constructor
  · rw [← Tagged.includeResults_iter, Tagged.outcomes_includeResults, repeat_empty, Set.image_empty]
  · rfl

private def checkpoint (w : W) (a : Unit) : Tagged W Unit (Unit ⊕ Unit) :=
  Tagged.withIncomplete () {1} (Tagged.includeResults (repeatBody w a))

private theorem checkpoint_body (w : W) (a : Unit) :
    (Elgot.ExceptT.body (checkpoint w) a).outcomes = {(.inl (.error ()), 1), (.inr a, w)} := by
  unfold Elgot.ExceptT.body
  rw [Finite.outcomes_bind_pure]
  change Prod.map Elgot.ExceptT.distribute id '' Tagged.outcomes (checkpoint w a) = _
  simp [checkpoint, Tagged.withIncomplete, repeatBody, Set.image_singleton,
    Tagged.outcomes_includeResults, Elgot.ExceptT.distribute]

private theorem checkpoint_run (w : W) {a : Unit} {r : Except Unit Unit} {v : W}
    (run : Finite.Runs (Elgot.ExceptT.body (checkpoint w)) a r v) :
    ∃ n : Nat, r = .error () ∧ v = w ^ n := by
  induction run with
  | done edge =>
    rw [checkpoint_body] at edge
    obtain ⟨rfl, rfl⟩ := by simpa using edge
    exact ⟨0, rfl, (pow_zero _).symm⟩
  | more edge _ ih =>
    rw [checkpoint_body] at edge
    obtain ⟨_, rfl⟩ := by simpa using edge
    obtain ⟨n, hr, hv⟩ := ih
    exact ⟨n + 1, hr, by rw [hv, pow_succ']⟩

private theorem checkpoint_power (w : W) (a : Unit) (n : Nat) :
    Finite.Runs (Elgot.ExceptT.body (checkpoint w)) a (.error ()) (w ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact .done (by simp [checkpoint_body])
  | succ n ih =>
    rw [pow_succ']
    exact .more (by simp [checkpoint_body]) ih

/-- Supplying the empty checkpoint before each recursive step yields exactly all
finite powers of the emitted log, tagged incomplete. -/
private theorem checkpoint_observations (w : W) (r : Except Unit Unit) (v : W) :
    (r, v) ∈ Tagged.outcomes (iter (checkpoint w) ()) ↔
      ∃ n : Nat, r = .error () ∧ v = w ^ n := by
  rw [Tagged.mem_iter]
  exact ⟨checkpoint_run w, fun ⟨n, hr, hv⟩ => hr.symm ▸ hv.symm ▸ checkpoint_power w () n⟩

private def allAtOnce (w : W) (_ : Unit) : Tagged W Unit (Unit ⊕ Unit) :=
  Tagged.ofOutcomes {p | ∃ n : Nat, p.1 = .error () ∧ p.2 = w ^ n}

/-- A single nondeterministic step offers logs of unbounded length and has the same
observations as the emitting loop. It has no recursive branch. -/
example (w : W) :
    Tagged.outcomes (iter (checkpoint w) ()) = Tagged.outcomes (iter (allAtOnce w) ()) ∧
    ∀ a next : Unit, ∀ v, (.ok (.inr next), v) ∉ Tagged.outcomes (allAtOnce w a) := by
  constructor
  · ext ⟨r, v⟩
    rw [checkpoint_observations, congrFun (LawfulElgotMonad.fixpoint (allAtOnce w)) (),
      Tagged.mem_bind]
    simp [allAtOnce]
    intro _ _
    exact ⟨fun h => ⟨(), h⟩, fun ⟨⟨⟩, h⟩ => h⟩
  · intro a next v
    simp [allAtOnce]

end Silmaril.Proofs.Semantics.NondeterministicTrace.Regression
