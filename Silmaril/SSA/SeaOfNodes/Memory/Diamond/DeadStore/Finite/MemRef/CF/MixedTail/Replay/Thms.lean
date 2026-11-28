module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {input : Tuple (Val cells) args} {entry : Memory.Graph args}
variable {requests : List Request}

/-- A replay step uses the mixed finder’s exact result at the saved input. -/
theorem check_accepted {request : Request} {stage : MixedTail.Result cells args preds}
    (checked : check fits arm suffix input entry request = some stage) :
    MixedTail.lower fits arm suffix input entry = some stage ∧ request.accepts stage.version = true :=
  Proofs.check_accepted checked

/-- Every step checks the retained entry and original occurrence bank. The
source CFG is the exact previous artifact, including at the stop. -/
theorem lower_trace :
    Trace fits arm suffix input entry (lowerBank preds fits cells (some entry) arm suffix) requests
      (lower preds fits entry arm suffix input requests) :=
  Proofs.lower_trace

/-- The returned result keeps its original typed input and emitted source,
and exposes the original request suffix beginning at the first refusal. -/
theorem lower_accounting :
    let result := lower preds fits entry arm suffix input requests
    result.programs.input = input ∧ result.programs.original = lowerBank preds fits cells (some entry) arm suffix ∧
      result.remaining = requests.drop result.deleted :=
  Proofs.lower_accounting

/-- Replaying the admitted versions produces the identical artifact chain
with all of those requests consumed. -/
theorem lower_replayed :
    let result := lower preds fits entry arm suffix input requests
    lower preds fits entry arm suffix input (result.admitted.map fun stage => .expect stage.version) =
      { result with remaining := [] } :=
  Proofs.lower_replayed

/-- The original Store count suffices to exhaust the represented mixed
checker on every surviving Store version. -/
theorem discover_exhausted :
    let retained := (discover preds fits entry arm suffix input).retained
    ∀ version ∈ storeVersions retained, tryVersion fits arm suffix input retained version = none :=
  Proofs.discover_exhausted

/-- At any shared CF budget the actual endpoints agree on the selected
occurrence, complete join packet, return word and final buffer. -/
theorem lower_observations (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower preds fits entry arm suffix input requests).programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial :=
  Proofs.lower_observations arrival fuel initial

/-- Preserve every entry Load and the Return word. The reported deletion
count is exact, and replaying the removed writes restores the entry buffer. -/
theorem lower_entry (initial : Buffer cells) :
    let result := lower preds fits entry arm suffix input requests
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      observe entry checkedInput initial = ((observe result.retained checkedInput initial).1, result.restoreEntry initial) ∧
      ∀ index, probe entry index = probe result.retained index :=
  Proofs.lower_entry initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay
