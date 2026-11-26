module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

private theorem evaluate_eq (job : Task carried) (state : State m.value carried out) :
    evaluate m g input job (dependencies m g input state job) = get (SCCP.transfer m g input state) job := by
  cases job with
  | control => exact Worklist.evaluate_eq m g input .control state
  | phi dst => exact Phi.evaluate_eq dst state
  | result => exact Worklist.evaluate_eq m g input .result state

private theorem update_eq (job : Task carried) (state : State m.value carried out) :
    update m g input job state = set state job (get (SCCP.transfer m g input state) job) := by
  unfold update
  rw [evaluate_eq]

private theorem get_update_self (job : Task carried) (state : State m.value carried out) :
    get (update m g input job state) job = get (SCCP.transfer m g input state) job := by
  rw [update_eq]
  cases job with
  | control => rfl
  | phi dst => exact Function.update_self _ _ _
  | result => rfl

private theorem get_update_other (job reader : Task carried) (state : State m.value carried out)
    (different : reader ≠ job) :
    get (update m g input job state) reader = get state reader := by
  rw [update_eq]
  cases job <;> cases reader <;> first
    | rfl
    | contradiction
    | exact Function.update_of_ne (fun equal => different (congrArg Job.phi equal)) _ _

private theorem le_update (job : Task carried) (state : State m.value carried out)
    (ascending : state ≤ SCCP.transfer m g input state) :
    state ≤ update m g input job state := by
  rw [update_eq]
  cases job with
  | control => exact ⟨ascending.1, le_rfl⟩
  | result => exact ⟨le_rfl, le_rfl, ascending.2.2⟩
  | phi dst =>
    refine ⟨le_rfl, ?_, le_rfl⟩
    intro reader
    change state.2.1 reader ≤ Function.update state.2.1 dst ((SCCP.transfer m g input state).2.1 dst) reader
    by_cases eq : reader = dst
    · subst reader
      rw [Function.update_self]
      exact ascending.2.1 dst
    · rw [Function.update_of_ne eq]

private theorem update_le (job : Task carried) (state upper : State m.value carried out)
    (below : state ≤ upper) (rhs : SCCP.transfer m g input state ≤ upper) :
    update m g input job state ≤ upper := by
  rw [update_eq]
  cases job with
  | control => exact ⟨rhs.1, below.2⟩
  | result => exact ⟨below.1, below.2.1, rhs.2.2⟩
  | phi dst =>
    refine ⟨below.1, ?_, below.2.2⟩
    intro reader
    change Function.update state.2.1 dst ((SCCP.transfer m g input state).2.1 dst) reader ≤ upper.2.1 reader
    by_cases eq : reader = dst
    · subst reader
      rw [Function.update_self]
      exact rhs.2.1 dst
    · rw [Function.update_of_ne eq]
      exact below.2.1 reader

theorem mem_wake_iff (old new : State m.value carried out) (pending : List (Task carried)) (job : Task carried) :
    job ∈ wake m g input old new pending ↔
      job ∈ pending ∨ dependencies m g input new job ≠ dependencies m g input old job := by
  have member : job ∈ jobs (dataPorts carried).length := by cases job <;> simp [jobs]
  simp [wake, FIFO.mem_wake_iff, member]

theorem step_nodup (job : Task carried) (state : State m.value carried out) {pending : List (Task carried)}
    (nodup : pending.Nodup) : (step m g input job state pending).2.Nodup := by
  have phis : ((List.finRange (dataPorts carried).length).map Job.phi).Nodup :=
    (List.nodup_finRange _).map (fun _ _ eq => Job.phi.inj eq)
  apply FIFO.wake_nodup _ _ nodup
  simp [jobs, List.nodup_append, phis]

private theorem wake_length (old new : State m.value carried out) (pending : List (Task carried)) :
    (wake m g input old new pending).length ≤ pending.length + (dataPorts carried).length.succ.succ := by
  unfold wake FIFO.wake
  rw [List.length_append]
  apply Nat.add_le_add_left
  exact List.length_filter_le _ _ |>.trans_eq (by simp [jobs])

theorem stable_step (job : Task carried) (state : State m.value carried out) (pending : List (Task carried))
    (stable : Stable m g input state (job :: pending)) :
    Stable m g input (step m g input job state pending).1 (step m g input job state pending).2 := by
  let new := update m g input job state
  intro reader absent
  have quiet := not_or.mp (fun seen => absent ((mem_wake_iff state new pending reader).mpr seen))
  have rhs := congrArg (evaluate m g input reader) (not_not.mp quiet.2)
  rw [evaluate_eq, evaluate_eq] at rhs
  by_cases current : reader = job
  · subst reader
    exact rhs.trans (get_update_self job state).symm
  · have old := stable reader (by simp [current, quiet.1])
    exact rhs.trans (old.trans (get_update_other job reader state current).symm)

theorem step_decreases (job : Task carried) (state : State m.value carried out) (pending : List (Task carried))
    (ascending : state ≤ SCCP.transfer m g input state) :
    potential (step m g input job state pending).1 (step m g input job state pending).2 <
      potential state (job :: pending) := by
  apply FIFO.potential_decreases _ _ (le_update job state ascending) (wake_length _ _ _)
  intro equal
  rw [show update m g input job state = state from equal]
  simp [wake, FIFO.wake]

private theorem initial_stable : Stable m g input ⊥ initial := by
  intro job absent
  cases job with
  | control => simp [initial] at absent
  | phi dst =>
    change phiFacts (∅ : Executable) (entryFacts m g input) (headerFacts m g input ⊥).feedback dst = ⊥
    simp [phiFacts, phiFact, gate]
    rfl
  | result => rfl

attribute [local irreducible] SCCP.solve

theorem run_spec : (run m g input).pending = [] ∧ solve m g input = SCCP.solve m g input := by
  let result := run m g input
  have final : result.pending = [] ∧ result.state ≤ SCCP.solve m g input ∧
      Stable m g input result.state result.pending :=
    FIFO.runSteps_checked (transfer_mono m g input) (fun job state _ => le_update job state)
      (fun job state _ upper => update_le job state upper) stable_step step_decreases
      (fun _ _ _ => Nat.zero_lt_succ _) _ _ _ _
      (solve_fixed m g input) bot_le bot_le initial_stable le_rfl
  have satisfied := final.2.2
  rw [final.1] at satisfied
  have fixed : SCCP.transfer m g input result.state = result.state :=
    Prod.ext (congrArg ULift.down (satisfied .control (by simp)))
      (Prod.ext (funext fun dst => satisfied (.phi dst) (by simp)) (satisfied .result (by simp)))
  exact ⟨final.1, le_antisymm final.2.1 ((solve_isLeast m g input).2 fixed)⟩

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Proofs
