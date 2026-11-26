module

public import Silmaril.SSA.MLIR.Complex.Defs
public import Silmaril.Numeric.Libm.Wasm.Defs

/-! # Binary64 adapters for scalar MLIR Math and Complex -/

@[expose] public section

namespace Silmaril.Wasm.SSA.MLIRMath

open Silmaril.MLIR Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm

/-- Reinterpret the MLIR encoding as the IEEE wrapper, preserving every bit. -/
def toF64 (bits : Math.Binary64) : F64 := F64.ofBits (UInt64.ofBitVec bits)

def ofF64 (x : F64) : Math.Binary64 := x.bits.toBitVec

/-- The exact rational value of a finite encoding, viewed as a real. -/
noncomputable def decodeFinite (bits : Math.Binary64) : Option ℝ :=
  (toF64 bits).toRat?.map fun q => (q : ℝ)

/-- The binary64 inputs covered by the positive-real logarithm reference. -/
def LogDomain (bits : Math.Binary64) : Prop :=
  ∃ x, decodeFinite bits = some x ∧ 0 < x

/-- Compare a binary64 logarithm result against nearest ties to even. -/
noncomputable def logRne : MathCollection.Observation Math.scalar Math.scalar where
  decodeInput := decodeFinite
  acceptOutput _ exactResult output := LibmFloat.CR exactResult (toF64 output)

/-- The value-only observation for a libm or Wasm logarithm candidate. -/
def LogNode (impl : F64 → Outcome F64) : Prop :=
  (Math.denote .log).RealizesOn logRne LogDomain fun bits output =>
    ofF64 (impl (toF64 bits)).value = output

/-- Require the returned encodings of the local `math.absf` evaluator. -/
def AbsFNode (impl : F64 → Outcome F64) : Prop :=
  ∀ x, (Math.denote .absf).Executes (ofF64 x) (ofF64 (impl x).value)

end Silmaril.Wasm.SSA.MLIRMath
