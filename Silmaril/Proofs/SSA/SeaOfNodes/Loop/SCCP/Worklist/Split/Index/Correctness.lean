module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Thms
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Proofs

open Diamond (Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact)
open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {value : Data → Type w}

/-- A direct carried read has singleton support for exactly the fact it reads. -/
private theorem numbered_read {n : Nat} {ports : List (Ty Data)} {t : Ty Data}
    (number : Fin ports.length → Fin n) (port : Port ports t)
    (left right : BankFacts value ports) :
    ∃ i, (Phi.Support.numberedPorts ports number).get port = {number i} ∧
      ((bankTuple left).get port = (bankTuple right).get port ↔ left i = right i) := by
  induction port with
  | head => exact ⟨0, rfl, Iff.rfl⟩
  | tail port ih =>
    obtain ⟨i, support, same⟩ := ih (fun j => number j.succ)
      (fun j => left j.succ) (fun j => right j.succ)
    exact ⟨i.succ, support, same⟩

private theorem arg_eq_iff {ports captures : List (Ty Data)} {t : Ty Data}
    (captured : Tuple (Fact value) captures) (port : Port (captures ++ ports) t)
    (left right : BankFacts value ports) :
    (appendTuple (bankTuple left) captured).get port = (appendTuple (bankTuple right) captured).get port ↔
      ∀ i ∈ (appendTuple (Phi.Support.numberedPorts ports id)
        (Phi.Support.emptyPorts ports.length captures)).get port, left i = right i := by
  induction captured with
  | nil =>
    obtain ⟨i, support, same⟩ := numbered_read (ports := ports) id port left right
    change (bankTuple left).get port = (bankTuple right).get port ↔
      ∀ j ∈ (Phi.Support.numberedPorts ports id).get port, left j = right j
    rw [support]
    simpa using same
  | cons head tail ih =>
    cases port with
    | head =>
      change head = head ↔ ∀ i ∈ (∅ : Finset (Fin ports.length)), left i = right i
      simp
    | tail port => exact ih port

variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {m : Model.{u, v, w} Op}
variable {input : Tuple (Fact m.value) (dataPorts inputs)}

/-- Changed marks or a changed supported field under feedback account for exactly
the differences in the reference Φ watch key. -/
private theorem watched_eq_iff (old new : State m.value carried out) (dst : Phi.Job carried) :
    Phi.dependencies m g input new dst = Phi.dependencies m g input old dst ↔
      (incomingIndex .entry ∈ old.1 ↔ incomingIndex .entry ∈ new.1) ∧
      (incomingIndex .backedge ∈ old.1 ↔ incomingIndex .backedge ∈ new.1) ∧
      (incomingIndex .backedge ∈ new.1 →
        ∀ field ∈ Phi.feedbackSupport g dst, new.2.1 field = old.2.1 field) := by
  have entry :
      ((decide (incomingIndex .entry ∈ new.1)) = (decide (incomingIndex .entry ∈ old.1))) ↔
        (incomingIndex .entry ∈ old.1 ↔ incomingIndex .entry ∈ new.1) := by
    by_cases hn : incomingIndex .entry ∈ new.1 <;> by_cases ho : incomingIndex .entry ∈ old.1 <;> simp [hn, ho]
  simp only [Phi.dependencies, Prod.mk.injEq, entry]
  apply and_congr_right
  intro _
  by_cases hn : incomingIndex .backedge ∈ new.1 <;> by_cases ho : incomingIndex .backedge ∈ old.1
  · cases wire : Phi.wireAt (g.phiInputs .backedge) dst with
    | arg port =>
      simpa [hn, ho, wire, Phi.feedbackSupport, Phi.Support.wire, Phi.Support.read, Phi.Support.headerPorts]
        using arg_eq_iff input port new.2.1 old.2.1
    | output node port =>
      simp [hn, ho, Phi.Support.restrictBank_eq_iff]
  all_goals simp [hn, ho]

variable [BankDecidableEq m.value (dataPorts carried)]

theorem mem_destinations_iff (index : Index g) (old new : State m.value carried out) (dst : Phi.Job carried) :
    dst ∈ index.destinations old new ↔ Phi.dependencies m g input new dst ≠ Phi.dependencies m g input old dst := by
  rw [ne_eq, watched_eq_iff]
  by_cases marks : (incomingIndex .entry ∈ old.1 ↔ incomingIndex .entry ∈ new.1) ∧
      (incomingIndex .backedge ∈ old.1 ↔ incomingIndex .backedge ∈ new.1)
  · obtain ⟨entry, feedback⟩ := marks
    by_cases enabled : incomingIndex .backedge ∈ new.1
    · simp [Index.destinations, gateDestinations, entry, feedback, enabled, Finset.mem_biUnion, index.mem_readers]
      constructor
      · rintro ⟨field, changed, read⟩
        exact ⟨field, read, changed⟩
      · rintro ⟨field, read, changed⟩
        exact ⟨field, changed, read⟩
    · simp [Index.destinations, gateDestinations, entry, feedback, enabled]
  · simp [Index.destinations, gateDestinations, marks, ← and_assoc]

theorem wake_eq (index : Index g) (old new : State m.value carried out) (pending : List (Task carried)) :
    Index.wake m index old new pending = Split.wake m g input old new pending := by
  have ordered :
      (index.destinations old new).sort.filter (fun dst => !pending.contains (.phi dst)) =
        (List.finRange (dataPorts carried).length).filter (fun dst =>
          !pending.contains (.phi dst) && decide (Phi.dependencies m g input new dst ≠
            Phi.dependencies m g input old dst)) := by
    apply List.SortedLT.eq_of_mem_iff
    · exact ((Finset.sortedLT_sort (index.destinations old new)).pairwise.filter _).sortedLT
    · exact ((List.sortedLT_finRange _).pairwise.filter _).sortedLT
    · intro dst
      simp only [List.mem_filter, Finset.mem_sort, List.mem_finRange, true_and, Bool.and_eq_true,
        decide_eq_true_eq]
      rw [mem_destinations_iff (m := m) (input := input)]
      exact and_comm
  unfold Index.wake Index.wakeDestinations wakeCandidates Split.wake FIFO.wake Split.jobs
  simp only [List.cons_append, List.filter_cons, List.filter_append, List.filter_map, List.filter_nil,
    Function.comp_def, Split.dependencies, Bool.and_true, ordered]
  rfl

theorem step_eq (index : Index g) (job : Task carried) (state : State m.value carried out)
    (pending : List (Task carried)) :
    Index.step m input index job state pending = Split.step m g input job state pending :=
  congrArg (Prod.mk (Split.update m g input job state)) (wake_eq index state _ pending)

private theorem changedAt_iff (job : Task carried) (state new : State m.value carried out)
    (updated : new = Split.update m g input job state) (field : Phi.Job carried) :
    new.2.1 field ≠ state.2.1 field ↔ job = .phi field ∧ bankChangedAfter job state new = true := by
  subst new
  let new := Split.update m g input job state
  change new.2.1 field ≠ state.2.1 field ↔ job = .phi field ∧ bankChangedAfter job state new = true
  by_cases same : job = .phi field
  · subst job
    simp [bankChangedAfter]
  · have unchanged : new.2.1 field = state.2.1 field := by
      cases job with
      | control | result => rfl
      | phi dst =>
        have different : field ≠ dst := fun eq => same (congrArg Job.phi eq.symm)
        exact Function.update_of_ne different _ _
    simp [same, unchanged]

theorem bankChangedAfter_iff (job : Task carried) (state : State m.value carried out) :
    let new := Split.update m g input job state
    bankChangedAfter job state new = true ↔ new.2.1 ≠ state.2.1 := by
  let new := Split.update m g input job state
  change bankChangedAfter job state new = true ↔ new.2.1 ≠ state.2.1
  rw [ne_eq, funext_iff, not_forall]
  simp only [changedAt_iff (m := m) (g := g) (input := input) job state new rfl]
  cases job <;> simp [bankChangedAfter]

theorem destinationsAfter_eq (index : Index g) (job : Task carried) (state : State m.value carried out) :
    let new := Split.update m g input job state
    index.destinationsAfter job state new = index.destinations state new := by
  let new := Split.update m g input job state
  change index.destinationsAfter job state new = index.destinations state new
  unfold Index.destinationsAfter Index.destinations Index.destinationsFromWrite
  apply congrArg (gateDestinations state.1 new.1)
  funext _
  apply Finset.ext
  intro reader
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    changedAt_iff (m := m) (g := g) (input := input) job state new rfl]
  cases job with
  | control | result => simp
  | phi dst => cases bankChangedAfter (.phi dst) state new <;> simp

omit [BankDecidableEq m.value (dataPorts carried)] in
private theorem gatedBankChanged_iff (mark : Fin 3) (old new : State m.value carried out)
    {changed : Bool} (bank : changed = true ↔ new.2.1 ≠ old.2.1) :
    gatedBankChanged mark old.1 new.1 changed = true ↔
      (if mark ∈ new.1 then some new.2.1 else none) ≠ (if mark ∈ old.1 then some old.2.1 else none) := by
  by_cases was : mark ∈ old.1 <;> by_cases now : mark ∈ new.1 <;> simp [gatedBankChanged, was, now, bank]

theorem gatedWatchesAfter_eq (job : Task carried) (state : State m.value carried out) :
    let new := Split.update m g input job state
    let changed := bankChangedAfter job state new
    gatedBankChanged (incomingIndex .entry) state.1 new.1 changed =
        decide (Worklist.dependencies new .control ≠ Worklist.dependencies state .control) ∧
      gatedBankChanged exitIndex state.1 new.1 changed =
        decide (Worklist.dependencies new .result ≠ Worklist.dependencies state .result) := by
  let new := Split.update m g input job state
  have bank := bankChangedAfter_iff (m := m) (g := g) (input := input) job state
  constructor
  · apply Bool.eq_iff_iff.mpr
    exact (gatedBankChanged_iff (incomingIndex .entry) state new bank).trans
      (decide_eq_true_iff (p := Worklist.dependencies new .control ≠ Worklist.dependencies state .control)).symm
  · apply Bool.eq_iff_iff.mpr
    exact (gatedBankChanged_iff exitIndex state new bank).trans
      (decide_eq_true_iff (p := Worklist.dependencies new .result ≠ Worklist.dependencies state .result)).symm

theorem stepLocal_eq (index : Index g) (job : Task carried) (state : State m.value carried out)
    (pending : List (Task carried)) :
    Index.stepLocal m input index job state pending = Index.step m input index job state pending := by
  let new := Split.update m g input job state
  let changed := bankChangedAfter job state new
  change (new, wakeCandidates (index.destinationsAfter job state new) (fun
    | .control => gatedBankChanged (incomingIndex .entry) state.1 new.1 changed
    | .phi _ => true
    | .result => gatedBankChanged exitIndex state.1 new.1 changed) pending) =
    (new, wake m index state new pending)
  rw [destinationsAfter_eq (m := m) (g := g) (input := input) index job state, Index.wake, Index.wakeDestinations]
  apply congrArg (Prod.mk new)
  apply congrArg (fun watched => wakeCandidates (index.destinations state new) watched pending)
  obtain ⟨control, result⟩ := gatedWatchesAfter_eq (m := m) (g := g) (input := input) job state
  funext notified
  cases notified with
  | control => exact control
  | phi _ => rfl
  | result => exact result

theorem runSteps_eq_step (index : Index g) :
    Index.runSteps m input index = FIFO.runSteps (Index.step m input index) :=
  congrArg FIFO.runSteps (funext fun job => funext fun state => funext fun pending =>
    stepLocal_eq index job state pending)

theorem runSteps_eq (index : Index g) :
    Index.runSteps m input index = Split.runSteps m g input := by
  have stepSame := funext fun job => funext fun state => funext fun pending =>
    step_eq (m := m) (input := input) index job state pending
  rw [runSteps_eq_step, Split.runSteps, stepSame]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Split.Index.Proofs
