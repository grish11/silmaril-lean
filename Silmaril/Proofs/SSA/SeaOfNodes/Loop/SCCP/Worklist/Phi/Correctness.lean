module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact readLocal tupleFacts)
open RVSDG (Locals Tuple Wires)
open Semantics.Dataflow (Flat)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}

private theorem read_wireAt {value : Data → Type w} {args ports : List (Ty Data)} {past : List (List (Ty Data))}
    (wires : Wires args past ports) (entry : Tuple (Fact value) args) (locals : Locals (Fact value) past)
    (job : Fin ports.length) :
    tupleFacts (wires.read entry locals) job = readLocal entry locals (wireAt wires job) := by
  induction wires with
  | nil => exact job.elim0
  | cons wire tail ih =>
    refine Fin.cases ?_ (fun i => ?_) job
    · cases wire <;> rfl
    · exact ih i

variable {m : Model.{u, v, w} Op} [eqBank : BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

theorem evaluate_eq (job : Job carried) (state : State m.value carried out) :
    evaluate m g input job (dependencies m g input state job) = (SCCP.transfer m g input state).2.1 job := by
  unfold evaluate dependencies
  change @Flat.join _ (eqBank.atPort job) _ _ = phiFacts state.1 (entryFacts m g input) (headerFacts m g input state.2.1).feedback job
  unfold phiFacts phiFact gate
  by_cases marked : incomingIndex .backedge ∈ state.1
  · simp only [ite_eq_left marked, decide_eq_true_eq]
    cases wire : wireAt (g.phiInputs .backedge) job with
    | output producer port => rfl
    | arg port =>
      congr 1
      let args := appendTuple (bankTuple state.2.1) input
      have read := read_wireAt (g.phiInputs .backedge) args (Diamond.SCCP.evalFacts m args g.header PUnit.unit) job
      erw [wire] at read
      exact read.symm
  · simp only [ite_eq_right marked, decide_eq_true_eq]

theorem mem_wake_iff (old new : State m.value carried out) (pending : List (Job carried)) (job : Job carried) :
    job ∈ wake m g input old new pending ↔
      job ∈ pending ∨ dependencies m g input new job ≠ dependencies m g input old job := by
  simp [wake, FIFO.mem_wake_iff]

theorem wake_nodup (old new : State m.value carried out) {pending : List (Job carried)}
    (nodup : pending.Nodup) : (wake m g input old new pending).Nodup := by
  exact FIFO.wake_nodup _ (List.nodup_finRange _) nodup

/-- The pending invariant needed by the enclosing loop worklist. -/
theorem step_stable (job : Job carried) (state : State m.value carried out) (pending : List (Job carried))
    (stable : ∀ dst, dst ∉ job :: pending →
      (SCCP.transfer m g input state).2.1 dst = state.2.1 dst) :
    let next := step m g input job state pending
    ∀ dst, dst ∉ next.2 → (SCCP.transfer m g input next.1).2.1 dst = next.1.2.1 dst := by
  intro next dst absent
  let updated := update m g input job state
  have quiet := not_or.mp (fun seen => absent ((mem_wake_iff state updated pending dst).mpr seen))
  have same := congrArg (evaluate m g input dst) (not_not.mp quiet.2)
  rw [evaluate_eq, evaluate_eq] at same
  change (SCCP.transfer m g input updated).2.1 dst = updated.2.1 dst
  rw [same]
  by_cases eq : dst = job
  · subst dst
    simp only [updated, update, write, Function.update_self]
    exact (evaluate_eq job state).symm
  · simp only [updated, update, write, Function.update_of_ne eq]
    exact stable dst (by simp [eq, quiet.1])

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Proofs
