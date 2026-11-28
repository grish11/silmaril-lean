module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse

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

/-- The invocation check tests the entry and every ordered occurrence. -/
theorem Contract.check_iff_valid (facts : Contract args preds) (input : Tuple (Val cells) args) :
    facts.check input = true ↔ facts.Valid input :=
  Proofs.check_iff_valid facts input

/-- The original accepted invocation satisfies the extracted contract. -/
theorem admitted_contract (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage) :
    (contractOf stage).Valid oldInput :=
  Proofs.admitted_contract accepted

/-- A successful reuse validates the contract and changes the saved input. -/
theorem reuse_eq_some_iff : reuse stage input = some reused ↔
    (contractOf stage).Valid input ∧ reused = atInput stage input :=
  Proofs.reuse_eq_some_iff

/-- Refusal corresponds exactly to a violated address obligation. -/
theorem reuse_eq_none_iff : reuse stage input = none ↔ ¬ (contractOf stage).Valid input :=
  Proofs.reuse_eq_none_iff

/-- The same nominated cut checks at any typed input satisfying the contract. -/
theorem tryVersion_atInput (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (valid : (contractOf stage).Valid input) :
    tryVersion fits arm suffix input entry stage.version = some (atInput stage input) :=
  Proofs.tryVersion_atInput accepted valid

/-- Reuse revalidates the nominated cut while preserving both exact CFGs. -/
theorem reuse_checked (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (rebound : reuse stage input = some reused) :
    tryVersion fits arm suffix input entry stage.version = some reused ∧
      reused.emission.programs.input = input ∧
      reused.emission.programs.original = stage.emission.programs.original ∧
      reused.emission.programs.optimized = stage.emission.programs.optimized :=
  Proofs.reuse_checked accepted rebound

/-- At the new input, every entry Load word and the Return word agree.
Reapplying the write restores the original entry buffer. -/
theorem reuse_entry (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (rebound : reuse stage input = some reused) (initial : Buffer cells) :
    let edit := reused.emission.edit
    let retained := observe edit.retained input initial
    let word := (observe edit.beforeStore input initial).1
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block input initial).1
    DeletesStores 1 (operations entry) (operations edit.retained) ∧
      observe entry input initial = (retained.1, ⟨Heap.write retained.2.cell (cell input edit.address) word⟩) ∧
      ∀ index, probe entry index = probe edit.retained index :=
  Proofs.reuse_entry accepted rebound initial

/-- Run both original artifacts at the new input. They select the same
occurrence and agree on the join packet, return and entire final buffer. -/
theorem reuse_observations (accepted : MixedTail.lower fits arm suffix oldInput entry = some stage)
    (rebound : reuse stage input = some reused) (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := stage.emission.programs
    let before := entryTransition programs.original input arrival initial
    let after := entryTransition programs.optimized input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized input arrival after.2 = armTransition programs.original input arrival before.2 ∧
      run programs.optimized input arrival fuel initial = run programs.original input arrival fuel initial :=
  Proofs.reuse_observations accepted rebound arrival fuel initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse
