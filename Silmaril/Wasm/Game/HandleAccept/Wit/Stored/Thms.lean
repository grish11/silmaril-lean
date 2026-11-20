module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored

open Silmaril.Formats Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {World : Type}

/-- Schema rejection performs no effects, including no resource or endpoint moves. -/
theorem lift_rejected (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (input : Input) {issue : Issue} (rejected : checkSchema type = .error issue) :
    lift (World := World) limits quirks cx type input = pure (.error issue) := by
  simp [lift, rejected]

/-- An admitted memory load runs the reference operations, retaining both their result and
their effects, after checking the pointer assertions required by the Canonical ABI. -/
theorem lift_memory_admitted (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (type : TypeOf) (ptr : Nat) (admitted : checkSchema type = .ok ()) :
    lift (World := World) limits quirks cx type (.memory ptr) = (do
      let width ← ptrType cx
      let layout := ABI.layout width type
      checkAligned ptr layout.alignment.bytes
      checkInBounds cx ptr layout.size
      return checkValue type (← loadAt limits quirks cx width type ptr)) := by
  simp [lift, admitted]

/-- An arity failure does not read payload memory or take ownership of an argument. -/
theorem buildNode_rejected_arity (sig : Signature) (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (tag : sig.Tag) (input : Input) (children : List (Tree sig))
    (bad : (sig.arity tag).Admits children.length = false) :
    buildNode (World := World) sig limits quirks cx tag input children = pure (.error .childArity) := by
  simp [buildNode, bad]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored
