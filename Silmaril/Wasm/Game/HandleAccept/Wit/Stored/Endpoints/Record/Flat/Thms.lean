module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.FlatSum

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

theorem lowerFlatAt_sum_program {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag : Nat) (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type) :
    (lowerFlatAt limits quirks cx width (.variant tag (Field.armValue arm)) type : P E World _) =
      lowerFlatVariantWith arms.length ((flatten width type).drop 1) tag
        (match arm with | none => [] | some field => flatten width field.type)
        (match arm with
         | none => pure []
         | some field => lowerFlatAt limits quirks cx width field.value field.type) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.FlatSum.sum_program limits quirks cx width type arms tag arm layout

/-- The sum emitter uses the reference flat effect program if its selected child does.
The comparison is program equality, including child traps, not just equal returned words.
The layout certificate aligns the tag, selected payload type, and full joined slot layout. -/
theorem runField_sum_flat_rejoin {E : CoreEngine} {World : Type}
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (width : AddrType) (type : TypeOf) (arms : List (Option TypeOf))
    (tag index : Nat) (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type)
    (child : ∀ field, arm = some field → Internal.runField limits quirks cx authority width field 0 .flat =
      Except.ok <$> lowerFlatAt limits quirks cx width field.value field.type) :
    Internal.runField limits quirks cx authority width (.sum type arms tag arm) index .flat =
      Except.ok <$> lowerFlatAt limits quirks cx width (.variant tag (Field.armValue arm)) type :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.FlatSum.sum_rejoin
    limits quirks cx authority width type arms tag index arm layout child

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
