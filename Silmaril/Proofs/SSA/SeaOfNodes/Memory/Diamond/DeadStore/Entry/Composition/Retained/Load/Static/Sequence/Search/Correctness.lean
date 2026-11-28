module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Thms
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Proofs

open RVSDG (Tuple)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)

variable {args : List ValueSort} {cells : Nat}
variable {entry : Memory.Graph args} {contracts : List (AddressContract args)}

theorem checkContracts_iff_valid (contracts : List (AddressContract args)) (input : Tuple (Val cells) args) :
    checkContracts contracts input = true ↔ ContractsValid contracts input := by
  simp [checkContracts, ContractsValid, AddressContract.check_iff_valid]

theorem find_checked {step : Step args} {retained : Memory.Graph args}
    (accepted : find entry contracts = some (step, retained)) :
    step.version ∈ storeVersions entry ∧ step.facts ∈ contracts ∧
      ∃ selected, Static.cut step.facts step.version entry = some (selected, retained) := by
  obtain ⟨version, versionMem, checked⟩ := List.exists_of_findSome?_eq_some accepted
  obtain ⟨facts, factsMem, cutResult⟩ := List.exists_of_findSome?_eq_some checked
  obtain ⟨⟨selected, tail⟩, edit, same⟩ := Option.map_eq_some_iff.mp cutResult
  cases same
  exact ⟨versionMem, factsMem, selected, edit⟩

theorem find_none_iff (entry : Memory.Graph args) (contracts : List (AddressContract args)) :
    find entry contracts = none ↔
      ∀ version ∈ storeVersions entry, ∀ facts ∈ contracts, Static.cut facts version entry = none := by
  simp [find, List.findSome?_eq_none_iff]

private theorem run_replays (contracts : List (AddressContract args)) (fuel : Nat) (entry : Memory.Graph args) :
    let result := run contracts fuel entry
    result.plan.rewrite entry = some result.entry ∧ ∀ step ∈ result.plan, step.facts ∈ contracts := by
  induction fuel generalizing entry with
  | zero => simp [run, Plan.rewrite]
  | succ fuel ih =>
    cases found : find entry contracts with
    | none => simp [run, found, Plan.rewrite]
    | some edit =>
      obtain ⟨step, retained⟩ := edit
      obtain ⟨_, factsMem, _, checked⟩ := find_checked found
      obtain ⟨replay, members⟩ := ih retained
      simp only [run, found]
      constructor
      · simp only [Plan.rewrite, List.foldlM_cons, checked, Option.map_some]
        exact replay
      · intro candidate member
        rcases List.mem_cons.mp member with rfl | tail
        · exact factsMem
        · exact members candidate tail

theorem discover_replays (entry : Memory.Graph args) (contracts : List (AddressContract args)) :
    let result := discover entry contracts
    result.plan.rewrite entry = some result.entry ∧ ∀ step ∈ result.plan, step.facts ∈ contracts :=
  run_replays contracts (storeCount entry) entry

private theorem step_storeCount {step : Step args} {retained : Memory.Graph args}
    (input : Tuple (Val cells) args) (valid : ContractsValid contracts input)
    (accepted : find entry contracts = some (step, retained)) :
    storeCount retained + 1 = storeCount entry := by
  obtain ⟨_, factsMem, _, checked⟩ := find_checked accepted
  exact (Static.cut_preserves checked (valid step.facts factsMem) (fun _ => 0)).1.storeCount_eq

private theorem run_exhausted (input : Tuple (Val cells) args) (valid : ContractsValid contracts input)
    (fuel : Nat) (entry : Memory.Graph args) (bound : storeCount entry ≤ fuel) :
    find (run contracts fuel entry).entry contracts = none := by
  induction fuel generalizing entry with
  | zero =>
    change find entry contracts = none
    cases accepted : find entry contracts with
    | none => rfl
    | some edit =>
      obtain ⟨step, retained⟩ := edit
      have decrease := step_storeCount input valid accepted
      omega
  | succ fuel ih =>
    cases accepted : find entry contracts with
    | none => simp only [run, accepted]
    | some edit =>
      obtain ⟨step, retained⟩ := edit
      have decrease := step_storeCount input valid accepted
      simpa only [run, accepted] using ih retained (by omega)

theorem discover_exhausted (input : Tuple (Val cells) args) (valid : ContractsValid contracts input) :
    ∀ version ∈ storeVersions (discover entry contracts).entry,
      ∀ facts ∈ contracts, Static.cut facts version (discover entry contracts).entry = none :=
  (find_none_iff _ _).mp (run_exhausted input valid (storeCount entry) entry (Nat.le_refl _))

theorem lower_error_iff (graph : Graph args) (entry : Memory.Graph args) (contracts : List (AddressContract args))
    (input : Tuple (Val cells) args) :
    lower graph entry contracts input = .error .invalidContracts ↔ ¬ ContractsValid contracts input := by
  rw [← checkContracts_iff_valid]
  cases checked : checkContracts contracts input <;> simp [lower, checked]

theorem lower_checked {graph : Graph args} {input : Tuple (Val cells) args} {emission : Emission cells args}
    (emitted : lower graph entry contracts input = .ok emission) :
    Sequence.lower graph entry emission.plan input = some emission.programs ∧
      ∀ version ∈ storeVersions emission.entry, ∀ facts ∈ contracts, Static.cut facts version emission.entry = none := by
  unfold lower at emitted
  split at emitted
  next checked =>
    cases Except.ok.inj emitted
    have valid := (checkContracts_iff_valid contracts input).mp checked
    obtain ⟨replay, members⟩ := discover_replays entry contracts
    refine ⟨?_, discover_exhausted input valid⟩
    exact (Sequence.lower_eq_some_iff _ _ _ _ _).mpr
      ⟨fun step member => valid step.facts (members step member), _, replay, rfl⟩
  next => contradiction

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Proofs
