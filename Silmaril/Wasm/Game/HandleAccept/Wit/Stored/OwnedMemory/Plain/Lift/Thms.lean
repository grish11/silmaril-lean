module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Plain.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.PlainLift

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

/-- The owner observer leaves canonical argument lifting unchanged for types with no
owner leaves read by this lift, including cursor updates and the one-pointer spill. -/
theorem liftFlatValues_plain {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (max : Nat) (cursor : FlatCursor) (types : List Stored.TypeOf)
    (plain : Stored.payloadTypesContainOwn types = false) :
    Prod.map (List.map Observed.ordinary) id <$> liftFlatValues limits quirks cx max cursor types =
      liftFlatValuesWith limits cx (flatCarrier (World := World) limits quirks cx) max cursor types :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.PlainLift.flatValues
    limits quirks cx max cursor types plain

/-- Checked memory and flat lifting preserve the entire canonical program for every
old admitted schema, not just the shape on success. -/
theorem lift_plain {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) {type : Stored.TypeOf} (admitted : Stored.checkSchema type = .ok ())
    (input : Stored.Input) :
    lift (World := World) limits quirks cx type input =
      (fun result => (result.map (Payload.equivPlain admitted)).mapError Issue.schema) <$>
        Stored.lift limits quirks cx type input :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.PlainLift.liftPlain
    limits quirks cx admitted input

/-- Preserve both typed rejections and constructed nodes, including the order and
contents of the already resolved children. -/
theorem buildNode_plain {E : CoreEngine} {World : Type} (sig : PlainSignature)
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E) (tag : sig.val.Tag)
    (input : Stored.Input) (children : List (Stored.Tree sig.val)) :
    buildNode (World := World) sig.val limits quirks cx tag input (children.map (Tree.equivPlain sig)) =
      (fun result => (result.map (Tree.equivPlain sig)).mapError Issue.schema) <$>
        Stored.buildNode sig.val limits quirks cx tag input children :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.PlainLift.nodePlain
    sig limits quirks cx tag input children

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
