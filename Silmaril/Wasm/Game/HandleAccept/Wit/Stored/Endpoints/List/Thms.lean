module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.List.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.ListLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value
open Silmaril.Wasm.Game.HandleAccept.Wit.Async (Channel Element)

theorem allocate_rejoin {E : CoreEngine} {World : Type} (cx : LiftLowerContext E)
    (layout : Layout) (storeElem : Val → Nat → P E World Unit) (entries : List Val) :
    storeListIntoRangeWith cx layout storeElem entries = (do
      let ptr ← allocateRange cx layout entries.length
      storeListIntoValidRangeWith layout.size storeElem entries ptr
      return (ptr, entries.length)) := rfl

theorem transfer_effect_order {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (cx : LiftLowerContext E) (channel : Channel) (element : Element) (id : EndId) :
    (transfer limits cx channel element id : P E (State sig) _) = (do
      match Lower.prepare (← getStore) (← hostGet) [.endpoint channel element id] with
      | .error issue => return .error issue
      | .ok next =>
        hostSet next
        modifyStore (HandleSt.setEndOwner id cx.inst)
        let slot ← handlesAdd cx.inst (.waitable (.end_ id))
        modifyStore (HandleSt.setEndIndex id slot)
        return .ok slot) := by
  simp only [transfer, lowerAsyncValue, bind_assoc, pure_bind]
  rfl

theorem lower_preflight_error {E : CoreEngine} {sig : Signature} (limits : Component.Limits)
    (cx : LiftLowerContext E) (channel : Channel) (element : Element)
    (payload : Payload (.list (endpointType channel element))) (output : Stored.Lower.Output)
    {issue : Lower.Issue} (reject : preflight cx channel element payload output = .error issue) :
    (lower limits cx channel element payload output : P E (State sig) _) =
      pure (.error (.beforeAllocation issue)) := by
  simp only [lower, reject]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.ListLower
