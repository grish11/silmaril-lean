module

public import Silmaril.Wasm.Component.Reference.ABI.Layout.Defs
import Silmaril.Proofs.Wasm.Component.Reference.LayoutBounds

public section

namespace Silmaril.Wasm.Component.ABI

/-- Each canonical record or tuple cursor placement fits inside the aligned
aggregate's representation, including padding and zero-sized fields. -/
theorem recordLayout_field_fits (fields : List Layout) (base index offset : Nat) (field : Layout)
    (aligned : (recordAlignment fields).bytes ∣ base)
    (member : fields[index]? = some field) (place : (fieldOffsets base fields)[index]? = some offset) :
    base ≤ offset ∧ offset % field.alignment.bytes = 0 ∧ offset + field.size ≤ base + (recordLayout fields).size :=
  Silmaril.Proofs.Wasm.Component.Reference.LayoutBounds.field_fits fields base index offset field aligned member place

end Silmaril.Wasm.Component.ABI
