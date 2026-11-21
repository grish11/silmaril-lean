module

public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

/-- The canonical saved frame for a collection allocator call. In particular
the frame captures no memory snapshot: range checks run after the return. -/
def listRangeResume {E : CoreEngine} {Host : Type} (cx : LiftLowerContext E) (area : Layout) (count : Nat)
    (finish : Nat → P E Host (Ret E)) (result : Ret E) : P E Host (Ret E) :=
  (match result with
   | .nat pointer => pure pointer
   | _ => internal "late-bound call: expected Ret.nat") >>= fun pointer =>
  validateListRange cx area count pointer >>= finish

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
