module

public import Silmaril.SSA.MLIR.Math.Binary64.Defs
import Init.Data.BitVec.Lemmas

public section

namespace Silmaril.MLIR.Math.Binary64

theorem abs_abs (x : Binary64) : abs (abs x) = abs x := by
  simp [abs, BitVec.and_assoc]

theorem neg_neg (x : Binary64) : neg (neg x) = x := by
  simp [neg, BitVec.xor_assoc]

end Silmaril.MLIR.Math.Binary64
