module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist.Proofs

open SeaOfNodes.Diamond (Model Signature ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq bankTuple)
open SeaOfNodes.Loop.SCCP.Worklist
open SeaOfNodes.Loop.SCCP.Worklist.Split (Job Task jobs)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts regs)]
variable {p : Program Op regs out} {input : Tuple (Fact m.value) (dataPorts regs)}

private theorem incoming_ne_exit (edge : Incoming) : incomingIndex edge ≠ exitIndex := by
  cases edge with
  | entry => decide
  | feedback side => cases side <;> decide

theorem evaluate_eq (job : Task regs) (state : State m.value regs out) :
    evaluate m p input job (dependencies state job) = get (transfer m p input state) job := by
  cases job with
  | control =>
    by_cases entry : incomingIndex .entry ∈ state.1 <;>
      simp [dependencies, evaluate, get, transfer, entry] <;> rfl
  | phi dst =>
    by_cases onTrue : incomingIndex (.feedback true) ∈ state.1 <;>
      by_cases onFalse : incomingIndex (.feedback false) ∈ state.1 <;>
      by_cases entry : incomingIndex .entry ∈ state.1 <;>
      simp [dependencies, evaluate, get, transfer, phiFacts, gate, columns, incoming_ne_exit,
        entry, onTrue, onFalse] <;> rfl
  | result =>
    by_cases exit : exitIndex ∈ state.1 <;> simp [dependencies, evaluate, get, transfer, gate, exit] <;> rfl

private theorem update_eq (job : Task regs) (state : State m.value regs out) :
    update m p input job state = set state job (get (transfer m p input state) job) := by
  unfold update
  rw [evaluate_eq]

private theorem get_update_self (job : Task regs) (state : State m.value regs out) :
    get (update m p input job state) job = get (transfer m p input state) job := by
  rw [update_eq]
  cases job with
  | control | result => rfl
  | phi dst => exact Function.update_self _ _ _

private theorem get_update_other (job reader : Task regs) (state : State m.value regs out)
    (different : reader ≠ job) :
    get (update m p input job state) reader = get state reader := by
  rw [update_eq]
  cases job <;> cases reader <;> first
    | rfl
    | contradiction
    | exact Function.update_of_ne (fun equal => different (congrArg Job.phi equal)) _ _

private theorem le_update (job : Task regs) (state : State m.value regs out)
    (ascending : state ≤ transfer m p input state) : state ≤ update m p input job state := by
  rw [update_eq]
  cases job with
  | control => exact ⟨ascending.1, le_rfl⟩
  | result => exact ⟨le_rfl, le_rfl, ascending.2.2⟩
  | phi dst =>
    refine ⟨le_rfl, ?_, le_rfl⟩
    intro reader
    change state.2.1 reader ≤ Function.update state.2.1 dst ((transfer m p input state).2.1 dst) reader
    by_cases equal : reader = dst
    · subst reader
      rw [Function.update_self]
      exact ascending.2.1 dst
    · rw [Function.update_of_ne equal]

private theorem update_le (job : Task regs) (state upper : State m.value regs out)
    (below : state ≤ upper) (rhs : transfer m p input state ≤ upper) : update m p input job state ≤ upper := by
  rw [update_eq]
  cases job with
  | control => exact ⟨rhs.1, below.2⟩
  | result => exact ⟨below.1, below.2.1, rhs.2.2⟩
  | phi dst =>
    refine ⟨below.1, ?_, below.2.2⟩
    intro reader
    change Function.update state.2.1 dst ((transfer m p input state).2.1 dst) reader ≤ upper.2.1 reader
    by_cases equal : reader = dst
    · subst reader
      rw [Function.update_self]
      exact rhs.2.1 dst
    · rw [Function.update_of_ne equal]
      exact below.2.1 reader

theorem mem_wake_iff (old new : State m.value regs out) (pending : List (Task regs)) (job : Task regs) :
    job ∈ wake old new pending ↔
      job ∈ pending ∨ dependencies new job ≠ dependencies old job := by
  have member : job ∈ jobs (dataPorts regs).length := by cases job <;> simp [jobs]
  simp [wake, FIFO.mem_wake_iff, member]

theorem step_nodup (job : Task regs) (state : State m.value regs out) {pending : List (Task regs)}
    (nodup : pending.Nodup) : (step m p input job state pending).2.Nodup := by
  have phis : ((List.finRange (dataPorts regs).length).map Job.phi).Nodup :=
    (List.nodup_finRange _).map (fun _ _ equal => Job.phi.inj equal)
  apply FIFO.wake_nodup _ _ nodup
  simp [jobs, List.nodup_append, phis]

private theorem wake_length (old new : State m.value regs out) (pending : List (Task regs)) :
    (wake old new pending).length ≤ pending.length + (dataPorts regs).length.succ.succ := by
  unfold wake FIFO.wake
  rw [List.length_append]
  apply Nat.add_le_add_left
  exact List.length_filter_le _ _ |>.trans_eq (by simp [jobs])

private theorem stable_step (job : Task regs) (state : State m.value regs out) (pending : List (Task regs))
    (stable : Stable m p input state (job :: pending)) :
    Stable m p input (step m p input job state pending).1 (step m p input job state pending).2 := by
  intro reader absent
  let new := update m p input job state
  change reader ∉ wake state new pending at absent
  have quiet := not_or.mp (fun seen => absent ((mem_wake_iff state new pending reader).mpr seen))
  have rhs := congrArg (evaluate m p input reader) (not_not.mp quiet.2)
  rw [evaluate_eq, evaluate_eq] at rhs
  change get (transfer m p input new) reader = get new reader
  by_cases current : reader = job
  · subst reader
    exact rhs.trans (get_update_self job state).symm
  · have old := stable reader (by simp [current, quiet.1])
    exact rhs.trans (old.trans (get_update_other job reader state current).symm)

theorem step_decreases (job : Task regs) (state : State m.value regs out) (pending : List (Task regs))
    (ascending : state ≤ transfer m p input state) :
    potential (step m p input job state pending).1 (step m p input job state pending).2 <
      potential state (job :: pending) := by
  apply FIFO.potential_decreases _ _ (le_update job state ascending) (wake_length _ _ _)
  intro equal
  rw [show update m p input job state = state from equal]
  simp [wake, FIFO.wake]

private theorem initial_stable : Stable m p input (⊥ : State m.value regs out) initial := by
  intro job absent
  cases job with
  | control => simp [initial] at absent
  | phi dst =>
    change phiFacts (∅ : Marked) _ dst = ⊥
    simp [phiFacts, gate]
  | result => rfl

attribute [local irreducible] SCCP.solve

theorem run_spec : (run m p input).pending = [] ∧ solve m p input = SCCP.solve m p input := by
  let result := run m p input
  have final : result.pending = [] ∧ result.state ≤ SCCP.solve m p input ∧
      Stable m p input result.state result.pending :=
    FIFO.runSteps_checked (transfer_mono m p input) (fun job state _ => le_update job state)
      (fun job state _ upper => update_le job state upper) stable_step step_decreases
      (fun _ _ _ => Nat.zero_lt_succ _) _ _ _ _
      (solve_fixed m p input) bot_le bot_le initial_stable le_rfl
  have satisfied := final.2.2
  rw [final.1] at satisfied
  have fixed : transfer m p input result.state = result.state :=
    Prod.ext (congrArg ULift.down (satisfied .control (by simp)))
      (Prod.ext (funext fun dst => satisfied (.phi dst) (by simp)) (satisfied .result (by simp)))
  exact ⟨final.1, le_antisymm final.2.1 ((solve_isLeast m p input).2 fixed)⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist.Proofs
