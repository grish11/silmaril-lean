module

public import Silmaril.Wasm.Component.Reference.WIT.Interp.Thms
import Silmaril.Proofs.Wasm.Component.Reference.WIT.InterpEndpoints

@[expose] public section

namespace Silmaril.Wasm.Component.WIT

universe u v

variable {Ref : Type u} {Resource : Type v} (E : Env Ref Resource)
  (futureEnd streamEnd : Option (ValType Ref Resource) → Type)

/-- The non-async types embed into the exact same syntax as the async-capable ones. -/
def SimpleType.embed : SimpleType Ref Resource ↪ ValType Ref Resource :=
  ⟨Subtype.val, Subtype.val_injective⟩

def SimpleType.ofType (type : ValType Ref Resource) : Option (SimpleType Ref Resource) :=
  if simple : type.simple = true then some ⟨type, simple⟩ else none

theorem SimpleType.ofType_embed (type : SimpleType Ref Resource) : ofType (embed type) = some type := by
  rcases type with ⟨type, simple⟩
  simp [ofType, embed, simple]

/-- Changing endpoint carriers does not change a non-async interpretation, even under compounds. -/
theorem SimpleType.interp_withEndpoints (type : SimpleType Ref Resource) :
    type.val.Interp (E.withEndpoints futureEnd streamEnd) = type.val.Interp E :=
  Silmaril.Proofs.Wasm.Component.Reference.WIT.InterpEndpoints.interp E futureEnd streamEnd
    type.val type.property

/-- The two value carriers are equivalent on the non-async fragment. -/
def SimpleType.extendValues (type : SimpleType Ref Resource) :
    type.val.Interp E ≃ type.val.Interp (E.withEndpoints futureEnd streamEnd) :=
  Equiv.cast (SimpleType.interp_withEndpoints E futureEnd streamEnd type).symm

/-- The same acceptor languages inhabit both versions of a non-async type. -/
def SimpleType.extendLanguages (type : SimpleType Ref Resource) :
    ValLang E type.val ≃ ValLang (E.withEndpoints futureEnd streamEnd) type.val :=
  Equiv.cast (congrArg Set (SimpleType.interp_withEndpoints E futureEnd streamEnd type).symm)

end Silmaril.Wasm.Component.WIT
