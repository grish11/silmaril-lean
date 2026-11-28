module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery

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

/-- Recovery preserves the original diagnostic, including the exact recorded
prefix and pending stages. -/
theorem lower_diagnostic :
    (lower original entry fits arm suffix input).diagnostic = Diagnostic.lower original entry input :=
  Proofs.lower_diagnostic

/-- On refusal, the resumed replay is exactly discovery on the residual typed
entry at the new input. Whole-chain acceptance skips fresh discovery. -/
theorem lower_fresh
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    let diagnostic := Diagnostic.lower original entry input
    (lower original entry fits arm suffix input).fresh = diagnostic.refusal.map fun _ =>
      Replay.discover preds fits diagnostic.checkedPrefix.replay.retained arm suffix input :=
  Proofs.lower_fresh recorded

/-- Each fresh cut starts on the preceding accepted CFG and typed entry under the
same invocation and ordered occurrence bank. -/
theorem lower_fresh_trace
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) {fresh : Replay.Result cells args preds}
    (resumed : (lower original entry fits arm suffix input).fresh = some fresh) :
    let accepted := (lower original entry fits arm suffix input).diagnostic.checkedPrefix.replay
    fresh.programs.original = accepted.programs.optimized ∧ fresh.programs.input = input ∧
      Replay.Trace fits arm suffix input accepted.retained accepted.programs.optimized (requestsFor accepted.retained) fresh :=
  Proofs.lower_fresh_trace recorded resumed

/-- When recovery admits no new cuts, it returns the exact recorded-prefix endpoint. -/
theorem lower_no_fresh_cuts
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original)
    (zero : ((lower original entry fits arm suffix input).fresh.map Replay.Result.deleted).getD 0 = 0) :
    let result := lower original entry fits arm suffix input
    let accepted := result.diagnostic.checkedPrefix.replay
    result.optimized = accepted.programs.optimized ∧ result.retained = accepted.retained :=
  Proofs.lower_no_fresh_cuts recorded zero

/-- The original and recovered actual artifacts agree on the selected occurrence,
complete join packet, returned word and whole final buffer at every common CF
budget. -/
theorem lower_observations
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let result := lower original entry fits arm suffix input
    let before := entryTransition original.programs.original input arrival initial
    let after := entryTransition result.optimized input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition result.optimized input arrival after.2 =
        armTransition original.programs.original input arrival before.2 ∧
      run result.optimized input arrival fuel initial = run original.programs.original input arrival fuel initial :=
  Proofs.lower_observations recorded arrival fuel initial

/-- The total deletion count is exact. The retained entry preserves the original
return word and every Load readback at its ordered read index. -/
theorem lower_entry
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (initial : Buffer cells) :
    let result := lower original entry fits arm suffix input
    let probe := fun (graph : Memory.Graph args) (index : Nat) => (throughLoad graph index).map fun block =>
      (observe block input initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe result.retained input initial).1 = (observe entry input initial).1 ∧
      ∀ index, probe entry index = probe result.retained index :=
  Proofs.lower_entry recorded initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery
