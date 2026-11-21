module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.MemorySum

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

theorem store_sum_program {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (type : TypeOf) (arms : List (Option TypeOf)) (tag ptr : Nat)
    (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type) :
    (store limits quirks cx (.variant tag (Field.armValue arm)) type ptr : P E World _) = (do
      let width ← ptrType cx
      let address ← storeVariantHead cx arms.length (maxCaseAlignment (arms.map (layoutOption width))) tag ptr
      match arm with
      | none => pure ()
      | some field => store limits quirks cx field.value field.type address) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.MemorySum.sum_program limits quirks cx type arms tag ptr arm layout

/-- After an explicit pointer-width read, a compiled sum writes the same discriminator
and selects the same aligned address as the canonical store. Program equality then
reduces to the reached child's program, including any child trap. This statement
does not replace a reached width read with a width cached before other effects. -/
theorem runField_sum_memory_rejoin {E : CoreEngine} {World : Type}
    (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (type : TypeOf) (arms : List (Option TypeOf)) (tag index ptr : Nat)
    (arm : Option Field) (layout : Field.LayoutMatches (.sum type arms tag arm) type)
    (child : ∀ width field address, arm = some field →
      Internal.runField limits quirks cx authority width field 0 (.memory address) =
        Except.ok <$> store limits quirks cx field.value field.type address) :
    (do
      let width ← ptrType cx
      Internal.runField limits quirks cx authority width (.sum type arms tag arm) index (.memory ptr)) =
      Except.ok <$> store limits quirks cx (.variant tag (Field.armValue arm)) type ptr :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.MemorySum.sum_rejoin
    limits quirks cx authority type arms tag index ptr arm layout child

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
