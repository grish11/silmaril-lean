module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Project

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory

open Silmaril.Wasm.Component Silmaril.Wasm.Component.ABI Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm (AddrType)

/-- Erasing the witnesses for the moved owners recovers the whole canonical
memory-lift program, including its effects and traps in their original order. -/
theorem project {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (type : TypeOf) (ptr : Nat) :
    Observed.value <$> loadAtWith limits cx width (carrier (World := World) limits quirks cx) type ptr =
      loadAt limits quirks cx width type ptr :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.project limits quirks cx width type ptr

/-- Erase only owner receipts, preserving the flat cursor, canonical effects and traps,
including those from indirect list and map elements. -/
theorem projectFlat {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (type : TypeOf) (cursor : FlatCursor) :
    Prod.map Observed.value id <$>
        liftFlatAtWith limits cx width (flatCarrier (World := World) limits quirks cx width) type cursor =
      liftFlatAt limits quirks cx width type cursor :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.projectFlat limits quirks cx width type cursor

/-- Erase receipts through the whole canonical caller start callback, not just a
successful value. This preserves progress, subtask state, spill checks, trap order,
and the shared argument cursor consumed by `lowerOnResolve`. -/
theorem projectLowerOnStart {E : CoreEngine} {World : Type} (limits : Component.Limits)
    (quirks : Quirks) (caller : CallerId) :
    List.map Observed.value <$> observeLowerOnStart (E := E) (World := World) limits quirks caller =
      lowerOnStart limits quirks caller :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.projectLowerOnStart limits quirks caller

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory
