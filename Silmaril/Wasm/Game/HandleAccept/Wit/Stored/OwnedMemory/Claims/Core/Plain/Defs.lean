module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Thms

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain

open Silmaril.Wasm.Execution.Core

/-- Preserve the arena, tree history and endpoint authority. Old states have no
owner receipts, and embedding observations does not create endpoint claims. -/
def embedWorld (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (state : Endpoints.Core.World grow sig.val) : World grow sig.val :=
  ⟨state.reference, ⟨state.writer.accepted.map (Tree.equivPlain sig), [], state.writer.held⟩⟩

/-- Compare the typed errors of the two existing dispatchers. `none` marks errors with
no old counterpart. This is an observation, not a fallback in the executable dispatcher. -/
def oldIssue : Issue → Option Endpoints.Core.Issue
  | .boundary issue => some issue
  | .localEffect issue => some (.localEffect issue)
  | .claims (.lift (.schema issue)) => some (.stored (.lift issue))
  | .claims .alias => some (.stored .alias)
  | _ => none

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain
