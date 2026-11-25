module

public import Init.Data.BitVec.Basic

/-! # Sign operations on encoded binary64 values -/

@[expose] public section

namespace Silmaril.MLIR.Math

/-- The scalar binary64 encoding, with the sign at bit 63. -/
abbrev Binary64 := BitVec 64

namespace Binary64

/-- Clear the sign bit, preserving the exponent and fraction. -/
def abs (x : Binary64) : Binary64 := x &&& 0x7fffffffffffffff

/-- Toggle the sign bit, preserving the exponent and fraction. -/
def neg (x : Binary64) : Binary64 := x ^^^ 0x8000000000000000

end Binary64
end Silmaril.MLIR.Math
