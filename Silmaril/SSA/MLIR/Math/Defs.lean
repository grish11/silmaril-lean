module

public import Silmaril.SSA.MLIR.Math.Collection.Defs
public import Silmaril.SSA.MLIR.Math.Binary64.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Scalar MLIR Math

The reference uses mathematical reals. The local executable `absf` acts on
binary64 encodings and accepts every bit pattern. The reference for `log` is
defined on positive reals and has no local executable implementation.
-/

@[expose] public section

namespace Silmaril.MLIR.Math

open MathCollection

abbrev scalar : ValueSort := ⟨ℝ, Binary64⟩

inductive Op : ValueSort → ValueSort → Type where
  | absf : Op scalar scalar
  | log : Op scalar scalar

def Op.executable : {a b : ValueSort} → Op a b → Option (a.encoded → b.encoded)
  | _, _, .absf => some Binary64.abs
  | _, _, .log => none

noncomputable def denote : Collection Op := fun op =>
  { executable := op.executable
    reference := match op with
      | .absf => .total abs
      | .log => ⟨(0 < ·), fun x _ => Real.log x⟩ }

end Silmaril.MLIR.Math
