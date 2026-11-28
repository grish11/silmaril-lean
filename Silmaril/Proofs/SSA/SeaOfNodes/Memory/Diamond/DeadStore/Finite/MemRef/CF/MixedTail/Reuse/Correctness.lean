module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Proofs

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Entry.Composition.Retained.Load.Static (AddressContract)
open Memory.Forwarding.Disjoint (Certificate cell)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open SeaOfNodes.Memory.MLIR.MemRef (observe)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {entry : Memory.Graph args} {oldInput input : Tuple (Val cells) args}
variable {stage reused : MixedTail.Result cells args preds}

theorem check_iff_valid (facts : Contract args preds) (input : Tuple (Val cells) args) :
    facts.check input = true ↔ facts.Valid input := by
  simp only [Contract.check, Contract.Valid, Bool.and_eq_true_iff, AddressContract.check_iff_valid]
  constructor
  · rintro ⟨entry, arms⟩
    exact ⟨entry, fun i => (facts.arms[i.val]).check_iff_valid input |>.mp
      (List.all_eq_true.mp arms i (List.mem_finRange i))⟩
  · rintro ⟨entry, arms⟩
    exact ⟨entry, List.all_eq_true.mpr fun i _ => (facts.arms[i.val]).check_iff_valid input |>.mpr (arms i)⟩

theorem admitted_contract (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage) :
    (contractOf stage).Valid oldInput := by
  obtain ⟨_, _, entry, _, arms, _⟩ := MixedTail.lower_checked accepted
  constructor
  · simpa [contractOf, AddressContract.Valid] using entry
  · intro i
    have checked := (Bool.and_eq_true_iff.mp (arms i)).1
    have valid := (Certificate.check_iff_valid ⟨stage.emission.edit.address, (stage.candidate i).readers⟩ oldInput).mp checked
    simpa [contractOf, AddressContract.Valid] using valid

theorem reuse_eq_some_iff : reuse stage input = some reused ↔
    (contractOf stage).Valid input ∧ reused = atInput stage input := by
  unfold reuse
  split
  next checked =>
    exact ⟨fun same => ⟨(check_iff_valid _ input).mp checked, (Option.some.inj same).symm⟩,
      fun valid => congrArg some valid.2.symm⟩
  next refused =>
    have invalid : ¬ (contractOf stage).Valid input := fun valid => refused ((check_iff_valid _ input).mpr valid)
    simp [invalid]

theorem reuse_eq_none_iff : reuse stage input = none ↔ ¬ (contractOf stage).Valid input := by
  simp [reuse, check_iff_valid]

theorem tryVersion_atInput (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (valid : (contractOf stage).Valid input) :
    tryVersion fits arm suffix input entry stage.version = some (atInput stage input) := by
  obtain ⟨_, found, _, inferred, arms, programs⟩ := MixedTail.lower_checked accepted
  have entryCheck : (Certificate.mk stage.emission.edit.address stage.ports).check input = true :=
    (stage.facts.check_iff_valid input).mpr valid.1.1
  have armCheck : LoadTail.PrefixWord.checkArms preds stage.emission.edit.address arm stage.candidate input = true := by
    apply List.all_eq_true.mpr
    intro i _
    let facts : Certificate args := ⟨stage.emission.edit.address, (stage.candidate i).readers⟩
    have readerFacts : facts.Valid input := by
      simpa [contractOf, AddressContract.Valid, facts] using valid.2 i
    exact Bool.and_eq_true_iff.mpr ⟨(facts.check_iff_valid input).mpr readerFacts,
      (Bool.and_eq_true_iff.mp (arms i)).2⟩
  cases stage
  dsimp only at found inferred entryCheck armCheck programs
  simp [MixedTail.tryVersion, found, inferred, entryCheck, armCheck, atInput, programs]

theorem reuse_checked (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (rebound : reuse stage input = some reused) :
    tryVersion fits arm suffix input entry stage.version = some reused ∧
      reused.emission.programs.input = input ∧
      reused.emission.programs.original = stage.emission.programs.original ∧
      reused.emission.programs.optimized = stage.emission.programs.optimized := by
  obtain ⟨valid, rfl⟩ := reuse_eq_some_iff.mp rebound
  exact ⟨tryVersion_atInput accepted valid, rfl, rfl, rfl⟩

theorem reuse_entry (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (rebound : reuse stage input = some reused) (initial : Buffer cells) :
    let edit := reused.emission.edit
    let retained := observe edit.retained input initial
    let word := (observe edit.beforeStore input initial).1
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block input initial).1
    DeletesStores 1 (operations entry) (operations edit.retained) ∧
      observe entry input initial = (retained.1, ⟨Heap.write retained.2.cell (cell input edit.address) word⟩) ∧
      ∀ index, probe entry index = probe edit.retained index := by
  obtain ⟨checked, saved, _, _⟩ := reuse_checked accepted rebound
  simpa only [saved] using MixedTail.tryVersion_entry checked initial

theorem reuse_observations (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (rebound : reuse stage input = some reused) (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := stage.emission.programs
    let before := entryTransition programs.original input arrival initial
    let after := entryTransition programs.optimized input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized input arrival after.2 = armTransition programs.original input arrival before.2 ∧
      run programs.optimized input arrival fuel initial = run programs.original input arrival fuel initial := by
  obtain ⟨checked, saved, original, optimized⟩ := reuse_checked accepted rebound
  simpa only [saved, original, optimized] using MixedTail.tryVersion_observations checked arrival fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Proofs
