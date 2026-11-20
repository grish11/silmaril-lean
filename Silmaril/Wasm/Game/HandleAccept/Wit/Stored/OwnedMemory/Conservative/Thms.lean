module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Conservative.Defs
public import Silmaril.Wasm.Game.HandleAccept.Wit.Fragments.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Conservative

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

/-- When the receipts are complete, forgetting them preserves the ordinary type check,
including the typed failure. A receipt mismatch is not an ordinary decoding error. -/
theorem erase_checkValue {type : Stored.TypeOf} (observed : Observed)
    (complete : observed.Complete type) :
    (checkValue type observed).map Payload.erase =
      (Stored.checkValue type observed.value).mapError Issue.schema :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Conservative.erase_checkValue observed complete

/-- The owner-aware checked lift is conservative on every WIT primitive, including
strings. This is equality of the reference effect programs after erasing successful
receipts, for either ABI input form and either linked address width. -/
theorem primitive_lift_conservative {E : CoreEngine} {World : Type} (limits : Component.Limits)
    (quirks : Quirks) (cx : LiftLowerContext E) (primitive : WIT.Primitive) (input : Stored.Input) :
    (fun result => result.map Payload.erase) <$>
        lift (World := World) limits quirks cx (.prim primitive) input =
      Except.mapError Issue.schema <$> Stored.lift limits quirks cx (.prim primitive) input :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Conservative.primitive_lift limits quirks cx primitive input

/-- The `ScalarType` embedding preserves checked lifting, not just the decoded values. -/
theorem scalar_lift_conservative {E : CoreEngine} {World : Type} (limits : Component.Limits)
    (quirks : Quirks) (cx : LiftLowerContext E) (scalar : ScalarType) (input : Stored.Input) :
    (fun result => result.map Payload.erase) <$>
        lift (World := World) limits quirks cx (.prim scalar.val) input =
      Except.mapError Issue.schema <$> Stored.lift limits quirks cx (.prim scalar.val) input :=
  primitive_lift_conservative limits quirks cx scalar.val input

/-- Building a primitive node gives exactly the old checked result after receipt
erasure, including arity rejection. Its already resolved children may be arbitrary. -/
theorem primitive_node_conservative {E : CoreEngine} {World : Type} (sig : Stored.Signature)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (tag : sig.Tag)
    (primitive : WIT.Primitive) (type : sig.payload tag = .prim primitive) (input : Stored.Input)
    (children : List (Tree sig)) :
    (fun result => result.map Tree.erase) <$>
        buildNode (World := World) sig limits quirks cx tag input children =
      Except.mapError Issue.schema <$>
        Stored.buildNode sig limits quirks cx tag input (children.map Tree.erase) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Conservative.primitive_node
    sig limits quirks cx tag primitive type input children

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
