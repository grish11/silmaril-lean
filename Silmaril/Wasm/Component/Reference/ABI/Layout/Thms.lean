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

/-- A selected variant payload fits its canonical slot after the tag. The
alignment includes all arms, even when only a smaller arm is selected. -/
theorem variantLayout_payload_fits (cases : List (Option Layout)) (base : Nat) (field : Layout)
    (aligned : (variantLayout cases).alignment.bytes ∣ base) (member : some field ∈ cases) :
    let offset := alignTo (base + (discriminantAlignment cases.length).bytes) (maxCaseAlignment cases)
    offset % field.alignment.bytes = 0 ∧ offset + field.size ≤ base + (variantLayout cases).size :=
  Silmaril.Proofs.Wasm.Component.Reference.LayoutBounds.variant_fits cases base field aligned member

end Silmaril.Wasm.Component.ABI
