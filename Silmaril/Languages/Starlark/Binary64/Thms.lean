module

public import Silmaril.Languages.Starlark.Binary64.Defs
import Silmaril.Proofs.Languages.Starlark.Binary64.Eval

public section

namespace Silmaril.Languages.Starlark.Binary64

/-- The bit-mask implementation returns exactly the specified magnitude encoding. -/
theorem absolute_iff_abs (input output : UInt64) : Absolute input output ↔ abs input = output :=
  Proofs.Languages.Starlark.Binary64.absolute_iff_abs input output

/-- The truth rules agree with the result of testing the magnitude encoding. -/
theorem truth_iff_truth (input : UInt64) (out : Bool) : Truth input out ↔ truth input = out :=
  Proofs.Languages.Starlark.Binary64.truth_iff_truth input out

/-- Exactly the two signed-zero encodings are false. -/
theorem truth_false_iff_signed_zero (input : UInt64) :
    truth input = false ↔ input = 0 ∨ input = 0x8000000000000000 :=
  Proofs.Languages.Starlark.Binary64.truth_false_iff_signed_zero input

/-- The bit-field rules recover exactly the denotational numeric observation. -/
theorem decodes_iff_decode (bits : UInt64) (value : Number) :
    Decodes bits value ↔ decode bits = value :=
  Proofs.Languages.Starlark.Binary64.decodes_iff_decode bits value

/-- The numeric order rules agree on the exact three-way comparison. -/
theorem orders_iff_compareNumbers (left right : Number) (order : Ordering) :
    Orders left right order ↔ compareNumbers left right = order :=
  Proofs.Languages.Starlark.Binary64.orders_iff_compareNumbers left right order

end Silmaril.Languages.Starlark.Binary64
