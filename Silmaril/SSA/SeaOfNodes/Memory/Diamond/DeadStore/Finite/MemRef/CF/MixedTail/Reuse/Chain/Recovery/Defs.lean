module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Defs

/-! Resume checked mixed-entry discovery after a recorded contract refuses. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  /-- The exact accepted recorded prefix, refusal and untouched pending stages. -/
  diagnostic : Diagnostic.Result cells args preds
  /-- Fresh discovery is attempted only after a refusal. Its stages are relative
  to the successive residual entries. An attempt can admit zero stages. -/
  fresh : Option (Replay.Result cells args preds)

def Result.optimized (result : Result cells args preds) : Program cells args preds :=
  (result.fresh.map fun fresh => fresh.programs.optimized).getD
    result.diagnostic.checkedPrefix.replay.programs.optimized

def Result.retained (result : Result cells args preds) : Memory.Graph args :=
  (result.fresh.map Replay.Result.retained).getD result.diagnostic.checkedPrefix.replay.retained

def Result.deleted (result : Result cells args preds) : Nat :=
  result.diagnostic.checkedPrefix.replay.deleted + (result.fresh.map Replay.Result.deleted).getD 0

/-- Use the same Store-count bound as fresh mixed-entry discovery. -/
def requestsFor (entry : Memory.Graph args) : List Replay.Request :=
  List.replicate (storeCount entry) .discover

/-- Opt in to recovery. Fresh requests start on the exact artifact and table
returned by the prefix rechecker. The original pending stages remain recorded
in the diagnostic and supply no requests or address evidence to recovery. -/
def lower (original : Replay.Result cells args preds) (entry : Memory.Graph args)
    (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) : Result cells args preds :=
  let diagnostic := Diagnostic.lower original entry input
  let accepted := diagnostic.checkedPrefix.replay
  ⟨diagnostic, diagnostic.refusal.map fun _ =>
    Replay.lowerFrom fits arm suffix accepted.programs.input (requestsFor accepted.retained)
      accepted.retained accepted.programs.optimized⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery
