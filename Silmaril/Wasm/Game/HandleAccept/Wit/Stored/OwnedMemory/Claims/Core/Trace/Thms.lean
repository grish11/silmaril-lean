module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Trace

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Trace

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace (CommitTag RootHistory roles)

/-- The receipt-aware Core boundary publishes exactly one root per observed successful
reply, in chronological order, for every permitted export session and its finite prefixes. -/
theorem history_of_session {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
    {memory : Option Nat} {state : World grow sig} {profile : Numerics.Profile} {module_ : Module}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × World grow sig} {tags : List CommitTag}
    (linked : module_.imports[contract.code]?.isSome = true)
    (session : TSession profile (env contract grow memory) module_ memory roles start state addrs
      phase pending current tags) : RootHistory state.writer.accepted current.2.writer.accepted tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Trace.history_of_session linked session

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Trace
