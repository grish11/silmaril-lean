module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Correctness

/-! One typed Φ visit implements one coordinate of the simultaneous equation. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}
variable {m : Model.{u, v, w} Op}
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

/-- Agreement on the transitive support suffices for the original feedback fact. -/
theorem feedback_agrees (job : Job carried) {left right : BankFacts m.value (dataPorts carried)}
    (same : ∀ i ∈ feedbackSupport g job, left i = right i) :
    (headerFacts m g input left).feedback job = (headerFacts m g input right).feedback job :=
  Proofs.feedback_agrees job same

variable [BankDecidableEq m.value (dataPorts carried)]

/-- Reading a job from one snapshot yields exactly its simultaneous right-hand side. -/
theorem evaluate_eq (job : Job carried) (state : State m.value carried out) :
    evaluate m g input job (dependencies m g input state job) = (SCCP.transfer m g input state).2.1 job :=
  Proofs.evaluate_eq job state

/-- A visit writes only its own typed coordinate, using the old assignment. -/
theorem update_eq (job : Job carried) (state : State m.value carried out) :
    update m g input job state = write state job ((SCCP.transfer m g input state).2.1 job) := by
  unfold update
  rw [evaluate_eq]

/-- Publishing distinct right-hand sides from one frozen snapshot commutes.
Re-evaluating a job after a write can yield a different right-hand side. -/
theorem write_comm (state snapshot : State m.value carried out) {first second : Job carried}
    (different : first ≠ second) :
    let rhs := (SCCP.transfer m g input snapshot).2.1
    write (write state first (rhs first)) second (rhs second) =
      write (write state second (rhs second)) first (rhs first) := by
  let rhs := (SCCP.transfer m g input snapshot).2.1
  have commute := Function.update_comm different (rhs first) (rhs second) state.2.1
  exact congrArg (fun bank => (state.1, bank, state.2.2)) commute

theorem mem_wake_iff (old new : State m.value carried out) (pending : List (Job carried)) (job : Job carried) :
    job ∈ wake m g input old new pending ↔
      job ∈ pending ∨ dependencies m g input new job ≠ dependencies m g input old job :=
  Proofs.mem_wake_iff old new pending job

theorem wake_nodup (old new : State m.value carried out) {pending : List (Job carried)}
    (nodup : pending.Nodup) : (wake m g input old new pending).Nodup :=
  Proofs.wake_nodup old new nodup

/-- If all absent Φ equations were satisfied, one pop and wake preserves that invariant. -/
theorem step_stable (job : Job carried) (state : State m.value carried out) (pending : List (Job carried))
    (stable : ∀ dst, dst ∉ job :: pending →
      (SCCP.transfer m g input state).2.1 dst = state.2.1 dst) :
    let next := step m g input job state pending
    ∀ dst, dst ∉ next.2 → (SCCP.transfer m g input next.1).2.1 dst = next.1.2.1 dst :=
  Proofs.step_stable job state pending stable

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi
