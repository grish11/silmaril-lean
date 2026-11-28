module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open SeaOfNodes.Memory.MLIR.MemRef (observe)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {input oldInput : Tuple (Val cells) args} {entry : Memory.Graph args}
variable {requests : List Replay.Request} {original : Replay.Result cells args preds}
/-- The executable whole-chain check validates every extracted contract. -/
theorem check_iff_valid : check original input = true ↔ Valid original input :=
  Proofs.check_iff_valid

/-- Each rechecked stage keeps its recorded version and links its exact
source CFG to the preceding optimized artifact. -/
theorem lower_trace
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    Trace fits arm suffix input entry original.programs.original original.admitted (lower original entry input) :=
  Proofs.lower_trace recorded

/-- The rebound stages are the admitted prefix, and the returned pending
stages are the original unaccepted suffix. -/
theorem lower_accounting
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    let result := lower original entry input
    result.replay.programs.input = input ∧ result.replay.programs.original = original.programs.original ∧
      result.replay.admitted =
        (original.admitted.take result.replay.deleted).map (fun stage => atInput stage input) ∧
      result.pending = original.admitted.drop result.replay.deleted :=
  Proofs.lower_accounting recorded

/-- Every stage rebinds exactly when the new input satisfies the whole chain. -/
theorem lower_complete
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    (lower original entry input).pending = [] ↔ Valid original input :=
  Proofs.lower_complete recorded

/-- The result keeps the exact last admitted CFG and typed entry, with
the original endpoints when the admitted prefix is empty. -/
theorem lower_endpoint
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    let result := lower original entry input
    (result.replay.programs.optimized, result.replay.retained) =
      (result.replay.admitted.getLast?.map fun stage =>
        (stage.emission.programs.optimized, stage.emission.edit.retained)).getD (original.programs.original, entry) :=
  Proofs.lower_endpoint recorded

/-- Complete acceptance reuses the exact old optimized CFG and retained entry. -/
theorem lower_complete_artifacts
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (complete : (lower original entry input).pending = []) :
    let result := (lower original entry input).replay
    result.programs.optimized = original.programs.optimized ∧ result.retained = original.retained :=
  Proofs.lower_complete_artifacts recorded complete

/-- At the new input the original CFG and accepted endpoint agree on the
selected occurrence, complete join packet and full return at any common budget. -/
theorem lower_observations
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower original entry input).replay.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial :=
  Proofs.lower_observations recorded arrival fuel initial

/-- At the new input the accepted chain preserves every entry Load word,
and replaying the removed writes reconstructs the original entry buffer. -/
theorem lower_entry
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (initial : Buffer cells) :
    let replay := (lower original entry input).replay
    let checkedInput := replay.programs.input
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores replay.deleted (operations entry) (operations replay.retained) ∧
      observe entry checkedInput initial = ((observe replay.retained checkedInput initial).1, replay.restoreEntry initial) ∧
      ∀ index, probe entry index = probe replay.retained index :=
  Proofs.lower_entry recorded initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain
