module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainCore

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

theorem embedWorld_injective (sig : PlainSignature) {grow : SingleThreaded.GrowOracle} :
    Function.Injective (embedWorld sig (grow := grow)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainCore.worldInjective sig

/-- Both checked imports perform the same arena effects and commit the same observation
or report corresponding typed errors. No new diagnostic is erased to an old success. -/
theorem attempt_plain (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) (memory : Option Nat) (state : Endpoints.Core.World grow sig.val)
    (call : UCall Nat) :
    let old := contract.attempt memory state call
    let new := Core.attempt contract memory (embedWorld sig state) call
    new.1 = embedWorld sig old.1 ∧ new.2.mapError oldIssue = old.2.mapError some :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainCore.attempt
    sig contract memory state call

variable {Entry Input Output Exit : Type}

/-- Every finite prefix of the actual receipt-aware Core session from an embedded state
has a legacy witness with the same tag sequence, Core configuration and embedded host state. -/
theorem session_plain_witness (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) {memory : Option Nat}
    {state : Endpoints.Core.World grow sig.val} {profile : Numerics.Profile} {module_ : Module}
    {roles : Roles Entry Input Output Exit} {start : Config Nat} {addrs : List Nat}
    {phase : Phase} {pending : Bool} {current : Config Nat × World grow sig.val}
    {tags : List (Silmaril.Accept.IO.Tag Entry Input Output Exit)}
    (session : TSession profile (Core.env contract grow memory) module_ memory roles start
      (embedWorld sig state) addrs phase pending current tags) :
    ∃ old, current.2 = embedWorld sig old ∧
      TSession profile (contract.env grow memory) module_ memory roles start state addrs
        phase pending (current.1, old) tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainCore.sessionBackward
    sig contract session

/-- The existing synchronous `accept-node` Core routes have exactly the same arbitrary
export sessions on plain signatures. This includes instantiation, trapping invocations,
retries and later exports, not only the calls that returned an accepted handle. -/
theorem session_plain_iff (sig : PlainSignature) {grow : SingleThreaded.GrowOracle}
    (contract : Contract sig.val) {memory : Option Nat}
    {state : Endpoints.Core.World grow sig.val} {profile : Numerics.Profile} {module_ : Module}
    {roles : Roles Entry Input Output Exit} {start : Config Nat} {addrs : List Nat}
    {phase : Phase} {pending : Bool} {current : Config Nat × Endpoints.Core.World grow sig.val}
    {tags : List (Silmaril.Accept.IO.Tag Entry Input Output Exit)} :
    TSession profile (Core.env contract grow memory) module_ memory roles start (embedWorld sig state)
      addrs phase pending (current.1, embedWorld sig current.2) tags ↔
    TSession profile (contract.env grow memory) module_ memory roles start state addrs
      phase pending current tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.PlainCore.sessionIff sig contract

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Plain
