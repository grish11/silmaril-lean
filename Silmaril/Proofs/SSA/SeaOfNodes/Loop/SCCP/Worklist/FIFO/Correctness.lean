module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Proofs

open Semantics.Dataflow.FiniteHeight (HeightBound)

variable {State Job : Type*}

theorem mem_wake_iff [DecidableEq Job] (jobs : List Job) (changed : Job → Bool) (pending : List Job) (job : Job) :
    job ∈ wake jobs changed pending ↔ job ∈ pending ∨ (job ∈ jobs ∧ changed job = true) := by
  by_cases present : job ∈ pending <;> simp [wake, present]

theorem wake_nodup [DecidableEq Job] {jobs pending : List Job} (changed : Job → Bool)
    (enumerated : jobs.Nodup) (nodup : pending.Nodup) : (wake jobs changed pending).Nodup := by
  unfold wake
  rw [List.nodup_append]
  refine ⟨nodup, enumerated.filter _, ?_⟩
  intro oldJob oldMem newJob newMem equal
  subst newJob
  simpa [oldMem] using (List.mem_filter.mp newMem).2

theorem potential_decreases [PartialOrder State] (height : HeightBound State) (jobs : Nat)
    {state new : State} {job : Job} {pending next : List Job}
    (ascending : state ≤ new) (size : next.length ≤ pending.length + jobs)
    (unchanged : new = state → next = pending) :
    potential height jobs new next < potential height jobs state (job :: pending) := by
  by_cases equal : new = state
  · rw [unchanged equal, equal]
    simp [potential]
  · have strict := height.rank_strict (lt_of_le_of_ne ascending (fun h => equal h.symm))
    have bound := height.rank_le new
    have remaining : height.bound - height.rank new + 1 ≤ height.bound - height.rank state := by omega
    have paid := Nat.mul_le_mul_right (jobs + 1) remaining
    rw [Nat.add_mul, Nat.one_mul] at paid
    simp only [potential, List.length_cons]
    omega

variable [PartialOrder State]
variable {transfer : State → State} {step : Job → State → List Job → State × List Job}
variable {stable : State → List Job → Prop} {measure : State → List Job → Nat}

/-- Drain a FIFO whose pops preserve the pending-equations invariant and
ascent, stay below the chosen fixed point, and decrease its potential. -/
theorem runSteps_checked
    (transfer_mono : Monotone transfer)
    (le_update : ∀ job state pending, state ≤ transfer state → state ≤ (step job state pending).1)
    (update_le : ∀ job state pending upper, state ≤ upper → transfer state ≤ upper → (step job state pending).1 ≤ upper)
    (stable_step : ∀ job state pending, stable state (job :: pending) →
      stable (step job state pending).1 (step job state pending).2)
    (decreases : ∀ job state pending, state ≤ transfer state →
      measure (step job state pending).1 (step job state pending).2 < measure state (job :: pending))
    (positive : ∀ job state pending, 0 < measure state (job :: pending))
    (fuel : Nat) (state upper : State) (pending : List Job)
    (fixed : transfer upper = upper) (ascending : state ≤ transfer state)
    (below : state ≤ upper) (invariant : stable state pending) (budget : measure state pending ≤ fuel) :
    let result := runSteps step fuel state pending
    result.pending = [] ∧ result.state ≤ upper ∧ stable result.state result.pending := by
  induction fuel generalizing state pending with
  | zero =>
    cases pending with
    | nil => exact ⟨rfl, below, invariant⟩
    | cons job rest => exact False.elim (Nat.not_lt_zero _ ((positive job state rest).trans_le budget))
  | succ fuel ih =>
    cases pending with
    | nil => exact ⟨rfl, below, invariant⟩
    | cons job rest =>
      let next := step job state rest
      have nextBudget := Nat.lt_succ_iff.mp ((decreases job state rest ascending).trans_le budget)
      have up := le_update job state rest ascending
      have ascending' : next.1 ≤ transfer next.1 :=
        (update_le job state rest _ ascending le_rfl).trans (transfer_mono up)
      have rhsBelow := (transfer_mono below).trans fixed.le
      exact ih _ _ ascending' (update_le job state rest upper below rhsBelow)
        (stable_step job state rest invariant) nextBudget

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Proofs
