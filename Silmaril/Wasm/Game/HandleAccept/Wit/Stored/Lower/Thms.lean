module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {World : Type}

/-- No reads or writes precede a rejected schema or a missing required ABI option. -/
theorem lower_rejected (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (payload : Payload type) (output : Output) {issue : Issue}
    (rejected : (checkSchema type >>= fun _ => checkOptions cx type output) = .error issue) :
    lower (World := World) limits quirks cx type payload output = pure (.error issue) := by
  simp [lower, rejected]

/-- Equality of effect programs: bounds, realloc, writes and traps are those of
the reference, not just equality of successful result values. -/
theorem lower_memory_reference (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (payload : Payload type) (ptr : Nat)
    (schema : checkSchema type = .ok ()) (options : checkOptions cx type (.memory ptr) = .ok ())
    (bounds : ∀ width, fits quirks cx.opts.encoding width type payload.val = true) :
    lower (World := World) limits quirks cx type payload (.memory ptr) = (do
      let width ← ptrType cx
      let area := layout width type
      let stored ← (do
        checkAligned ptr area.alignment.bytes
        checkInBounds cx ptr area.size
        Canon.store limits quirks cx payload.val type ptr)
      return .ok stored) := by
  have ready : (checkSchema type >>= fun _ => checkOptions cx type (.memory ptr)) = .ok () := by
    rw [schema]
    exact options
  simp [lower, ready, bounds, emit]
  rfl

/-- Flat lowering preserves the reference's coercions, padding, and effects. -/
theorem lower_flat_reference (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (payload : Payload type) (schema : checkSchema type = .ok ())
    (options : checkOptions cx type .flat = .ok ())
    (bounds : ∀ width, fits quirks cx.opts.encoding width type payload.val = true) :
    lower (World := World) limits quirks cx type payload .flat = (do
      let width ← ptrType cx
      return .ok (← lowerFlatAt limits quirks cx width payload.val type)) := by
  have ready : (checkSchema type >>= fun _ => checkOptions cx type .flat) = .ok () := by
    rw [schema]
    exact options
  simp [lower, ready, bounds, emit]
  rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Lower
