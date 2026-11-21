module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Defs
public import Silmaril.Wasm.Component.Reference.Canon.Store.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordStoreInv

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

variable {E : CoreEngine} {World : Type} {I : CStore E → Prop}

/-- The recursive checked interpreter preserves the store invariant locally,
including its memory writes, handle leaves, discriminator writes and the
post-allocation checks. Late-bound calls must be certified by the scheduler. -/
theorem runField_inv (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (width : AddrType) (preserves : P.Inv.StorePres I)
    (prepare : ∀ plan, P.Inv I (authority.prepare plan))
    (transfer : ∀ index object, P.Inv I (authority.transfer index object))
    (field : Field) (index : Nat) (output : Stored.Lower.Output) :
    P.Inv I (Internal.runField limits quirks cx authority width field index output) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordStoreInv.field_inv
    limits quirks cx authority width preserves prepare transfer field index output

theorem compiledValue_inv (limits : Component.Limits) (quirks : Quirks) (cx : LiftLowerContext E)
    (authority : Authority E World) (preserves : P.Inv.StorePres I)
    (prepare : ∀ plan, P.Inv I (authority.prepare plan))
    (transfer : ∀ index object, P.Inv I (authority.transfer index object))
    (type : TypeOf) (value : Val) (output : Stored.Lower.Output)
    (compiled : Except Issue (Field × List Object)) :
    P.Inv I (Internal.lowerWithPlan quirks cx authority type value compiled Field.objects fun reached field =>
      Internal.emitValue limits quirks cx authority reached type field output) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.RecordStoreInv.compiled_value_inv
    limits quirks cx authority preserves prepare transfer type value output compiled

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower
