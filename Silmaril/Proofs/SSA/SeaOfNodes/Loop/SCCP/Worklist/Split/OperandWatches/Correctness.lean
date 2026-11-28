module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.FIFO.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {g : Graph Op inputs carried entrySigs headerSigs out}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

omit [BankDecidableEq m.value (dataPorts carried)] in
private theorem gate_quiet (mark : Fin 3) (old new : Executable) (changed : Bool)
    (quiet : Index.gatedBankChanged mark old new changed = false) :
    (mark ∈ new ↔ mark ∈ old) ∧ (mark ∈ new → changed = false) := by
  by_cases was : mark ∈ old <;> by_cases now : mark ∈ new <;>
    simp_all [Index.gatedBankChanged]

private theorem agrees_of_miss (support : Finset (Phi.Job carried)) (job : Task carried)
    (state new : State m.value carried out) (updated : new = Split.update m g input job state)
    (quiet : hits job support (Index.bankChangedAfter job state new) = false) :
    ∀ field ∈ support, new.2.1 field = state.2.1 field := by
  intro field member
  by_contra different
  obtain ⟨rfl, wrote⟩ := (Index.fieldChangedAfter_iff job state new updated field).mp different
  simp [hits, wrote, member] at quiet

/-- A quiet control watch leaves the control equation unchanged across the pop. -/
theorem control_eq_of_quiet (watches : OperandWatches g) (job : Task carried)
    (state new : State m.value carried out) (updated : new = Split.update m g input job state)
    (quiet : watches.candidateChanged job state.1 new.1 (Index.bankChangedAfter job state new) .control = false) :
    Split.get (SCCP.transfer m g input new) .control = Split.get (SCCP.transfer m g input state) .control := by
  obtain ⟨marks, misses⟩ := gate_quiet (incomingIndex .entry) state.1 new.1 _ quiet
  change (⟨SCCP.control new.1 (headerFacts m g input new.2.1).guard⟩ : ULift Executable) =
    ⟨SCCP.control state.1 (headerFacts m g input state.2.1).guard⟩
  by_cases enabled : incomingIndex .entry ∈ new.1
  · have agrees := agrees_of_miss watches.guardPorts job state new updated (misses enabled)
    rw [watches.guardPorts_eq] at agrees
    have guard : (headerFacts m g input new.2.1).guard = (headerFacts m g input state.2.1).guard :=
      Phi.Support.wire_agrees (m := m) g.header g.predicate input agrees
    simp [SCCP.control, enabled, marks.mp enabled, guard]
  · have oldDisabled : incomingIndex .entry ∉ state.1 := fun old => enabled (marks.mpr old)
    simp [SCCP.control, enabled, oldDisabled]

/-- A quiet result watch leaves the gated result equation unchanged across the pop. -/
theorem result_eq_of_quiet (watches : OperandWatches g) (job : Task carried)
    (state new : State m.value carried out) (updated : new = Split.update m g input job state)
    (quiet : watches.candidateChanged job state.1 new.1 (Index.bankChangedAfter job state new) .result = false) :
    Split.get (SCCP.transfer m g input new) .result = Split.get (SCCP.transfer m g input state) .result := by
  obtain ⟨marks, misses⟩ := gate_quiet exitIndex state.1 new.1 _ quiet
  change gate new.1 exitIndex (headerFacts m g input new.2.1).result =
    gate state.1 exitIndex (headerFacts m g input state.2.1).result
  by_cases enabled : exitIndex ∈ new.1
  · have agrees := agrees_of_miss watches.resultPorts job state new updated (misses enabled)
    rw [watches.resultPorts_eq] at agrees
    have result : (headerFacts m g input new.2.1).result = (headerFacts m g input state.2.1).result :=
      Phi.Support.wire_agrees (m := m) g.header g.result input agrees
    simp [gate, enabled, marks.mp enabled, result]
  · have oldDisabled : exitIndex ∉ state.1 := fun old => enabled (marks.mpr old)
    simp [gate, enabled, oldDisabled]

private theorem quiet_wake (watches : OperandWatches g) (job : Task carried)
    (state : State m.value carried out) (pending : List (Task carried)) (reader : Task carried)
    (absent : reader ∉ wakeAfter watches job state (Split.update m g input job state) pending) :
    reader ∉ pending ∧ Split.get (SCCP.transfer m g input (Split.update m g input job state)) reader =
      Split.get (SCCP.transfer m g input state) reader := by
  let new := Split.update m g input job state
  let candidates := .control :: (watches.index.destinationsAfter job state new).sort.map Job.phi ++ [.result]
  let changed := watches.candidateChanged job state.1 new.1 (Index.bankChangedAfter job state new)
  change reader ∉ FIFO.wake candidates changed pending at absent
  rw [FIFO.mem_wake_iff] at absent
  obtain ⟨unpending, quiet⟩ := not_or.mp absent
  refine ⟨unpending, ?_⟩
  cases reader with
  | control =>
    apply control_eq_of_quiet watches job state new rfl
    cases differs : changed .control with
    | false => exact differs
    | true => exact False.elim (quiet ⟨by simp [candidates], differs⟩)
  | result =>
    apply result_eq_of_quiet watches job state new rfl
    cases differs : changed .result with
    | false => exact differs
    | true => exact False.elim (quiet ⟨by simp [candidates], differs⟩)
  | phi dst =>
    have deps : Phi.dependencies m g input new dst = Phi.dependencies m g input state dst := by
      by_contra different
      have member := (Index.mem_destinations_iff watches.index state new dst).mpr different
      rw [← Index.destinationsAfter_eq (m := m) (input := input) watches.index job state] at member
      have actual : dst ∈ watches.index.destinationsAfter job state new := member
      exact quiet ⟨by simp [candidates, actual], rfl⟩
    change (SCCP.transfer m g input new).2.1 dst = (SCCP.transfer m g input state).2.1 dst
    rw [← Phi.evaluate_eq dst new, ← Phi.evaluate_eq dst state, deps]

private theorem candidates_length (destinations : Finset (Phi.Job carried)) :
    (.control :: destinations.sort.map Job.phi ++ [.result] : List (Task carried)).length ≤
      (dataPorts carried).length.succ.succ := by
  have size := Finset.card_le_univ destinations
  simp only [Fintype.card_fin] at size
  simpa [List.cons_append, Nat.add_assoc] using Nat.add_le_add_right size 2

private theorem wake_length (watches : OperandWatches g) (job : Task carried)
    (old new : State m.value carried out) (pending : List (Task carried)) :
    (wakeAfter watches job old new pending).length ≤ pending.length + (dataPorts carried).length.succ.succ := by
  unfold wakeAfter Index.wakeCandidates FIFO.wake
  rw [List.length_append]
  exact Nat.add_le_add_left ((List.length_filter_le _ _).trans (candidates_length _)) _

private theorem wake_unchanged (watches : OperandWatches g) (job : Task carried)
    (state : State m.value carried out) (pending : List (Task carried)) :
    wakeAfter watches job state state pending = pending := by
  have unchanged : Index.bankChangedAfter job state state = false := by
    cases job <;> simp [Index.bankChangedAfter]
  have noDestinations : watches.index.destinationsFromWrite job state.1 state.1 false = ∅ := by
    cases job <;> simp [Index.destinationsFromWrite, Index.gateDestinations]
  have noHits (support : Finset (Phi.Job carried)) : hits job support false = false := by
    cases job <;> simp [hits]
  simp [wakeAfter, unchanged, noDestinations, noHits, candidateChanged, Index.gatedBankChanged,
    Index.wakeCandidates, FIFO.wake]

theorem run_spec (watches : OperandWatches g) :
    (run m input watches).pending = [] ∧ solve m input watches = SCCP.solve m g input :=
  Split.run_with_wake m g input (wakeAfter watches) (quiet_wake watches)
    (wake_length watches) (wake_unchanged watches)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.OperandWatches.Proofs
