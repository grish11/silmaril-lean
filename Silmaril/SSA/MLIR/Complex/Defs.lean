module

public import Silmaril.SSA.MLIR.Math.Defs
public import Mathlib.Basic.Complex.Basic

/-! # Scalar MLIR Complex

The exact carrier is Mathlib's complex numbers. The executable carrier is an
ordered pair of binary64 encodings. Construction and projections preserve
component encodings, and conjugation toggles the imaginary sign bit.
-/

@[expose] public section

namespace Silmaril.MLIR.Complex

open MathCollection

abbrev complex : ValueSort := ⟨ℂ, Math.Binary64 × Math.Binary64⟩

inductive Op : ValueSort → ValueSort → Type where
  | create : Op (Math.scalar.pair Math.scalar) complex
  | re : Op complex Math.scalar
  | im : Op complex Math.scalar
  | conj : Op complex complex

def Op.executable : {a b : ValueSort} → Op a b → a.encoded → b.encoded
  | _, _, .create => id
  | _, _, .re => Prod.fst
  | _, _, .im => Prod.snd
  | _, _, .conj => fun z => (z.1, Math.Binary64.neg z.2)

noncomputable def denote : Collection Op := fun op =>
  { executable := some op.executable
    reference := .total (match op with
      | .create => fun parts => ⟨parts.1, parts.2⟩
      | .re => _root_.Complex.re
      | .im => _root_.Complex.im
      | .conj => star) }

/-- Lift a partial scalar decoding through the ordered component pair. -/
def decodeParts (decode : Math.Binary64 → Option ℝ)
    (parts : Math.Binary64 × Math.Binary64) : Option (ℝ × ℝ) := do
  let re ← decode parts.1
  let im ← decode parts.2
  return (re, im)

/-- Observe `create` through exact decoded component values. -/
def createObservation (decode : Math.Binary64 → Option ℝ) :
    Observation (Math.scalar.pair Math.scalar) complex :=
  .exact (decodeParts decode) (fun bits =>
    (decodeParts decode bits).map (fun parts => ⟨parts.1, parts.2⟩))

end Silmaril.MLIR.Complex
