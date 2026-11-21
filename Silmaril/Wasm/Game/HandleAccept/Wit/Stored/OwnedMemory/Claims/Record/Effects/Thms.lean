module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CheckedCanonicalEffects

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower (Field)

variable {E : CoreEngine} {World : Type} {sig : Signature}

/-- The emitter and its checked canonical effect view are the same program,
not just equal when successful. Control after a realloc observes the returned
store; typed refusals return through the saved continuation, traps do not. -/
theorem emitValue_eq (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (type : TypeOf) (item : Field) (output : Lower.Output) :
    Endpoints.RecordLower.Internal.emitValue limits quirks cx (authority access limits cx) width type item output =
      root access limits quirks cx width type item output :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CheckedCanonicalEffects.root
    access limits quirks cx width type item output

/-- Select the same compiled program after whole-schema preflight, ordered dry-run
reservation and the destination width/fit check, for either public give ABI. -/
theorem lowerValue_eq (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (payload : OwnedMemory.Payload type) (output : Lower.Output) :
    Record.lowerValue access limits quirks cx type payload output =
      Endpoints.RecordLower.Internal.lowerWithPlan quirks cx (authority access limits cx) type payload.val.value
        (preflightValue cx type payload output) Field.objects
        (fun width item => root access limits quirks cx width type item output) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.CheckedCanonicalEffects.lowerValue
    access limits quirks cx type payload output

theorem lowerPayloadRoot_eq (access : Access E World sig) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tree : Tree sig) (output : Lower.Output) :
    Record.lowerPayloadRoot access limits quirks cx tree output = lowerTree access limits quirks cx tree output := by
  cases tree with
  | atom impossible => exact impossible.elim
  | tag payload _ _ => exact lowerValue_eq access limits quirks cx (sig.payload payload.1) payload.2 output

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Record.Effects
