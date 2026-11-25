module

public import Silmaril.Wasm.Numerics.Integer

public section

namespace SqliteWasm.VarintContinuation

/-- The correction after appending the next seven-bit digit in the quoted reader
moves the bit-14 correction to bit 7 of the previous accumulator before shifting. -/
theorem appendAfterContinuation (acc byte : BitVec 64) :
    (acc <<< 7 ^^^ byte) ^^^ 16384#64 =
      ((acc ^^^ 128#64) <<< 7) ^^^ byte := by
  rw [BitVec.shiftLeft_xor_distrib]
  rw [show (128#64 <<< (7 : Nat)) = 16384#64 from by decide +kernel]
  ac_rfl

#print axioms appendAfterContinuation

end SqliteWasm.VarintContinuation
