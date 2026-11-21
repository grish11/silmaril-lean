module

public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs
public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

open Machine Machine.ReturnFrame.Occurrence in
/-- The real allocator return pops the top program frame. Only a subsequent
range trap clears the remaining active occurrences; saved storage is not popped. -/
def RangeReturnTrails {E : CoreEngine} {Host : Type} (profile : ProfileKind) (ready : HostReady Host)
    (dispatch : Call E → P E Host (Ret E)) (before : Config E Host) (labels : List (Label E Host))
    (after : Config E Host) (trapped : Bool := false) : Prop :=
  ∀ mark : Option Location,
    let popped := mark.bind (Edit.pop : Edit E Host).follow
    Trail profile ready dispatch before mark labels after (if trapped then popped.bind (Edit.clear : Edit E Host).follow else popped)

/-- The canonical saved frame for a collection allocator call. In particular
the frame captures no memory snapshot: range checks run after the return. -/
def listRangeResume {E : CoreEngine} {Host : Type} (cx : LiftLowerContext E) (area : Layout) (count : Nat)
    (finish : Nat → P E Host (Ret E)) (result : Ret E) : P E Host (Ret E) :=
  (match result with
   | .nat pointer => pure pointer
   | _ => internal "late-bound call: expected Ret.nat") >>= fun pointer =>
  validateListRange cx area count pointer >>= finish

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
