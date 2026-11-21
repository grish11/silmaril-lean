module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.CanonicalTree.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Record.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CanonicalTree

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.CanonicalTree

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Value

/-- The recursive canonical-side view is the actual reference program, not just
an agreement on successful values. This equality retains allocator requests,
their continuations, width reads, descriptor writes and canonical traps. It
does not erase or discharge the checked emitter's authority or bounds guards. -/
theorem field_canonical {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (item : Field) (type : TypeOf)
    (checked : item.LayoutMatches type) (out : Lower.Output) :
    field limits quirks cx width item out = (leaf limits quirks cx width item out : P E World out.Result) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Endpoints.CanonicalTree.canonical
    limits quirks cx width item type checked out

/-- Substitute the value and layout certificates supplied by public payload
preflight. This identifies the reference side without granting live authority. -/
theorem field_reference {E : CoreEngine} {World : Type} (limits : Component.Limits) (quirks : Quirks)
    (cx : LiftLowerContext E) (width : AddrType) (item : Field) (type : TypeOf) (value : Val)
    (checked : item.LayoutMatches type) (represents : item.value = value) (out : Lower.Output) :
    field limits quirks cx width item out = Lower.Output.rec (motive := fun out => P E World out.Result)
      (fun ptr => store limits quirks cx value type ptr) (lowerFlatAt limits quirks cx width value type) out := by
  rw [field_canonical limits quirks cx width item type checked out]
  cases out <;> simp only [leaf, checked.type_eq, represents] <;> rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.RecordLower.CanonicalTree
