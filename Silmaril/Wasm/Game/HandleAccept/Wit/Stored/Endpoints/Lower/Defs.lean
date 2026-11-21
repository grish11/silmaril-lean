module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

def Internal.directIssue : RecordLower.Issue → Issue
  | .preflight issue | .field _ (.beforeAllocation issue) | .field _ (.afterAllocation issue) => issue
  | .nested _ issue => Internal.directIssue issue
  | .ownerReceipt | .claims _ => .schema .ownedResourceNeedsIdentity
  | .notRecord | .unsupportedField _ => .decodedType

/-- The allocation-free endpoint route uses the shared recursive emitter. It keeps
its typed ABI refusals, but spends each claim at its transfer instead of reconstructing
spent claims from the reached store after a trap. -/
def lower {E : CoreEngine} {sig : Signature} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type)
    (output : Stored.Lower.Output) : P E (State sig) (Except Issue output.Result) :=
  match preflight cx type payload output with
  | .error issue => pure (.error issue)
  | .ok _ => do
    let authority := RecordLower.Internal.endpointAuthority limits cx
    let result ← RecordLower.Internal.lowerWithPlan quirks cx authority type payload.val
      (RecordLower.compileValue cx type payload.val [] output) RecordLower.Field.objects
      (fun width field => RecordLower.Internal.emitValue limits quirks cx authority width type field output)
    return result.mapError Internal.directIssue

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower
