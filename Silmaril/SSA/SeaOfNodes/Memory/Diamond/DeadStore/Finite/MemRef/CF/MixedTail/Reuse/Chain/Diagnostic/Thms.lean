module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open LoadTail.PrefixWord.Sequence.Replay.Search (inferCandidate)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {input oldInput : Tuple (Val cells) args} {stage : MixedTail.Result cells args preds}
variable {conflict : Alias cells args preds} {report : Refusal cells args preds}
variable {entry : Memory.Graph args} {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args}
variable {suffix : Memory.Graph (.word :: args)}
variable {requests : List Replay.Request} {original : Replay.Result cells args preds}

/-- The wrapper returns the existing rechecker result verbatim, including
the selected CFG, typed entry and untouched pending suffix. -/
theorem lower_prefix :
    (lower original entry input).checkedPrefix = Chain.lower original entry input := rfl

/-- The ordered search has no coinciding cell exactly when the recorded contract
holds. -/
theorem alias_none_iff : alias? stage input = none ↔ (contractOf stage).Valid input :=
  Proofs.alias_none_iff

/-- The witness selects the recorded port at this site and gives its common cell
with the nominated Store. -/
theorem alias_sound (found : alias? stage input = some conflict) : conflict.Valid stage input :=
  Proofs.alias_sound found

/-- The wrapper has no refusal exactly when the checked replay has no pending
stages. -/
theorem lower_none_iff
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) :
    (lower original entry input).refusal = none ↔ (Chain.lower original entry input).pending = [] :=
  Proofs.lower_none_iff recorded

/-- The rejected stage starts the untouched pending suffix, with its original cut
and ordered occurrence evidence on the exact preceding CFG and typed entry.
Its identified port coincides with the nominated Store at the new input. -/
theorem lower_refusal
    (recorded : Replay.Trace fits arm suffix oldInput entry (lowerBank preds fits cells (some entry) arm suffix)
      requests original) (explained : (lower original entry input).refusal = some report) :
    let checkedPrefix := (lower original entry input).checkedPrefix
    ∃ stage rest, checkedPrefix.pending = stage :: rest ∧
      original.admitted.drop report.stageIndex = stage :: rest ∧
      report.stageIndex = checkedPrefix.replay.deleted ∧ report.version = stage.version ∧
      report.store = stage.emission.edit.address ∧
      stage.emission.programs.original = checkedPrefix.replay.programs.optimized ∧
      inferCut report.version checkedPrefix.replay.retained = some (stage.emission.edit, stage.ports) ∧
      inferCandidate preds report.store arm = some stage.candidate ∧
      reuse stage input = none ∧ report.conflict.Valid stage input :=
  Proofs.lower_refusal recorded explained

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic
