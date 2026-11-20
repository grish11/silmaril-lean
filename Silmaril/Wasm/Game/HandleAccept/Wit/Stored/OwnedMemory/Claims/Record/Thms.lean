module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints

/-- A successful whole-plan dry run authorizes each nominal owner or readable
endpoint at most once. Error contexts are shared and do not enter the claim list. -/
theorem prepare_distinct {E : CoreEngine} {sig : Signature} (store : CStore E)
    (state : State sig) (plan : List RecordLower.Object) (checked : prepare store state plan = .ok ()) :
    (exclusiveSpends plan).Nodup :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.RecordPrepare.prepare_distinct
    store state plan checked

theorem lower_preflight_error {E : CoreEngine} {World : Type} {sig : Signature} (access : Access E World sig)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf)
    (payload : Payload type) (output : Stored.Lower.Output) {issue : RecordLower.Issue}
    (reject : preflight cx type payload output = .error issue) :
    lower access limits quirks cx type payload output = pure (.error issue) := by
  simp only [lower, RecordLower.Internal.lowerCompiled, RecordLower.Internal.lowerWithPlan, reject]

theorem lowerValue_preflight_error {E : CoreEngine} {World : Type} {sig : Signature}
    (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (payload : Payload type) (output : Stored.Lower.Output) {issue : RecordLower.Issue}
    (reject : preflightValue cx type payload output = .error issue) :
    lowerValue access limits quirks cx type payload output = pure (.error issue) := by
  simp only [lowerValue, RecordLower.Internal.lowerWithPlan, reject]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record
