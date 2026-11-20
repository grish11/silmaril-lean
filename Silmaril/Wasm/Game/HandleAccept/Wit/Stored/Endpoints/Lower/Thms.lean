module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

theorem afterTrap_held {E : CoreEngine} {sig : Signature} (store : CStore E) (plan : List Object)
    (state : State sig) (id : EndId) :
    id ∈ (afterTrap store plan state).held ↔ id ∈ state.held ∧ transferred store plan id = false := by
  simp [afterTrap]

/-- A schema or ABI refusal happens even before reading the reference store or claims. -/
theorem lower_preflight_error {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (quirks : Quirks) (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type)
    (output : Stored.Lower.Output) {issue : Issue}
    (reject : preflight cx type payload output = .error issue) :
    (lower limits quirks cx type payload output : P E (State sig) _) = pure (.error issue) := by
  simp only [lower, reject]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Lower
