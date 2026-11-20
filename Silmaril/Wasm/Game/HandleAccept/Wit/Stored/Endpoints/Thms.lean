module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element Endpoint Channel.endKind)

/-- Spending a claim does not remove an accepted tree or leave a copy of the claim. -/
theorem spend_preserves_observations {sig : Signature} {state updated : State sig} {id : EndId}
    (spent : state.spend id = .ok updated) : updated.accepted = state.accepted ∧ id ∉ updated.held := by
  unfold State.spend at spent
  split at spent <;> cases spent
  simp

/-- A retained observation does not make a spent claim spendable again. -/
theorem spend_no_second_give {sig : Signature} {state updated : State sig} {id : EndId}
    (spent : state.spend id = .ok updated) : updated.spend id = .error .unclaimed := by
  simp [State.spend, (spend_preserves_observations spent).2]

/-- No path reaches table insertion while the host still holds this claim. Each refusal
branch issues only the reads needed for validation. -/
theorem give_effect_order {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (cx : LiftLowerContext E) (channel : Channel) (element : Element)
    (endpoint : Endpoint (channel.endKind .read) element) :
    (give limits cx channel element endpoint : P E (State sig) _) = (do
      match (← hostGet).spend endpoint.id with
      | .error issue => return .error issue
      | .ok updated =>
        match Async.Transfer.readyToGive (← getStore) channel element endpoint with
        | .error issue => return .error (.give issue)
        | .ok () =>
          hostSet updated
          modifyStore (HandleSt.setEndOwner endpoint.id cx.inst)
          let slot ← handlesAdd cx.inst (.waitable (.end_ endpoint.id))
          modifyStore (HandleSt.setEndIndex endpoint.id slot)
          return .ok slot) := by
  simp only [give, lowerAsyncValue, bind_assoc, pure_bind]
  rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints
