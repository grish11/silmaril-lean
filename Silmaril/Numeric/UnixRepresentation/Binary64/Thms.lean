module

public import Silmaril.Numeric.UnixRepresentation.Binary64.Defs
import Silmaril.Proofs.Numeric.UnixRepresentation.Binary64

public section

namespace Silmaril.Numeric.UnixRepresentation.Binary64

open Timestamp
open Ieee754

variable {kind : Kind} {source target payloadUnit : TickUnit}

/-- NaNs and infinities are rejected under every tick rounding policy. -/
theorem decode_eq_nonfinite_iff (payload : F64) (kind : Kind) (payloadUnit target : TickUnit)
    (rounding : TickRounding) :
    decode kind payload payloadUnit target rounding = .error .nonfinite ↔ ¬payload.IsFinite :=
  Proofs.Numeric.UnixRepresentation.Binary64.decode_eq_nonfinite_iff payload kind payloadUnit
    target rounding

/-- Exact decoding succeeds precisely when the scaled payload equals the returned integer. -/
theorem decode_exact_eq_ok_iff {payload : F64} {result : Ticks kind target} :
    decode kind payload payloadUnit target .exact = .ok result ↔
      decodeCount? payload payloadUnit target = some (result.ticks : ℚ) :=
  Proofs.Numeric.UnixRepresentation.Binary64.decode_exact_eq_ok_iff

/-- Flooring discards a nonnegative offset smaller than one destination tick. -/
theorem decode_floor_bounds {payload : F64} {q : ℚ} {result : Ticks kind target}
    (h : decodeCount? payload payloadUnit target = some q)
    (decoded : decode kind payload payloadUnit target .floor = .ok result) :
    (result.ticks : ℚ) ≤ q ∧ q < (result.ticks : ℚ) + 1 :=
  Proofs.Numeric.UnixRepresentation.Binary64.decode_floor_bounds h decoded

/-- Truncation discards less than one destination tick in the direction of zero. -/
theorem decode_trunc_bounds {payload : F64} {q : ℚ} {result : Ticks kind target}
    (h : decodeCount? payload payloadUnit target = some q)
    (decoded : decode kind payload payloadUnit target .trunc = .ok result) :
    (0 ≤ q → (result.ticks : ℚ) ≤ q ∧ q < (result.ticks : ℚ) + 1) ∧
      (q < 0 → q ≤ (result.ticks : ℚ) ∧ (result.ticks : ℚ) < q + 1) :=
  Proofs.Numeric.UnixRepresentation.Binary64.decode_trunc_bounds h decoded

/-- The overflow threshold includes the tie between maximum finite and 2^1024. -/
theorem encodeRne_eq_overflow_iff (value : Ticks kind source) (payloadUnit : TickUnit) :
    encodeRne value payloadUnit = .error .overflow ↔
      RationalRounding.overflowThreshold ≤ |count value payloadUnit| :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeRne_eq_overflow_iff value payloadUnit

/-- Successful encoding is finite and selects the nearest magnitude, with the even index on ties. -/
theorem encodeRne_finite_nearestEven {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    payload.IsFinite ∧
      AdjacentRounding.NearestEven RationalRounding.magnitude |count value payloadUnit|
        (Binary64Signs.magnitudeBits payload.bits).toNat :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeRne_finite_nearestEven encoded

/-- The encoding retains the sign of a negative count and assigns zero the positive sign. -/
theorem encodeRne_signBit {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    payload.signBit = decide (count value payloadUnit < 0) :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeRne_signBit encoded

/-- Both signed zeros decode to the epoch under every policy and unit pair. -/
theorem decode_signedZero (negative : Bool) (kind : Kind) (payloadUnit target : TickUnit)
    (rounding : TickRounding) :
    decode kind (F64.ofBits (if negative then 0x8000000000000000 else 0))
      payloadUnit target rounding = .ok ⟨0⟩ :=
  Proofs.Numeric.UnixRepresentation.Binary64.decode_signedZero negative kind payloadUnit
    target rounding

@[simp] theorem encodeExact_zero (kind : Kind) (source payloadUnit : TickUnit) :
    encodeExact (⟨0⟩ : Ticks kind source) payloadUnit = .ok (F64.ofBits 0) :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeExact_zero kind source payloadUnit

/-- The exact signed error is minimal among all finite binary64 payloads. -/
theorem encodeRne_nearest {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    ∃ rounded : ℚ, payload.toRat? = some rounded ∧
      ∀ (candidate : F64) (exact : ℚ), candidate.toRat? = some exact →
        |count value payloadUnit - rounded| ≤ |count value payloadUnit - exact| :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeRne_nearest encoded

/-- Exact encoding returns the RNE payload precisely when it preserves the rational count. -/
theorem encodeExact_eq_ok_iff {value : Ticks kind source} {payload : F64} :
    encodeExact value payloadUnit = .ok payload ↔
      encodeRne value payloadUnit = .ok payload ∧ payload.toRat? = some (count value payloadUnit) :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeExact_eq_ok_iff

/-- Exact encoding followed by exact decoding recovers the original kind, unit and ticks. -/
theorem encodeExact_roundtrip {value : Ticks kind source} {payload : F64}
    (encoded : encodeExact value payloadUnit = .ok payload) :
    decode kind payload payloadUnit source .exact = .ok value :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeExact_roundtrip encoded

/-- Decoding and re-encoding exactly recovers the finite rational payload value. -/
theorem decodeExact_roundtrip {payload : F64} {value : Ticks kind target}
    (decoded : decode kind payload payloadUnit target .exact = .ok value) :
    ∃ result, encodeExact value payloadUnit = .ok result ∧ result.toRat? = payload.toRat? :=
  Proofs.Numeric.UnixRepresentation.Binary64.decodeExact_roundtrip decoded

/-- Exact encoding requires a count below the overflow threshold with a finite exact encoding. -/
theorem encodeExact_exists_iff {value : Ticks kind source} :
    (∃ payload, encodeExact value payloadUnit = .ok payload) ↔
      |count value payloadUnit| < RationalRounding.overflowThreshold ∧
        ∃ candidate : F64, candidate.toRat? = some (count value payloadUnit) :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeExact_exists_iff

/-- An integral payload-unit count with magnitude at most 2^53 encodes exactly. -/
theorem encodeExact_of_int {value : Ticks kind source} {n : Int}
    (integer : count value payloadUnit = (n : ℚ)) (bounded : n.natAbs ≤ 2 ^ 53) :
    ∃ payload, encodeExact value payloadUnit = .ok payload :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeExact_of_int integer bounded

/-- For finite RNE output, the absolute error is at most half the spacing of
    the interval bracketing the input magnitude, in the payload unit. -/
theorem encodeRne_halfUlp {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    ∃ rounded : ℚ, payload.toRat? = some rounded ∧
      |count value payloadUnit - rounded| ≤ ulp (count value payloadUnit) / 2 :=
  Proofs.Numeric.UnixRepresentation.Binary64.encodeRne_halfUlp encoded

/-- Below 2^53 payload units of magnitude, adjacent encodings are at most one unit apart. -/
theorem ulp_le_one {q : ℚ} (bounded : |q| < (2 : ℚ) ^ (53 : Nat)) : ulp q ≤ 1 :=
  Proofs.Numeric.UnixRepresentation.Binary64.ulp_le_one bounded

/-- Below 2^53 payload units of magnitude, RNE error is at most half a payload unit. -/
theorem encodeRne_halfTick {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload)
    (bounded : |count value payloadUnit| < (2 : ℚ) ^ (53 : Nat)) :
    ∃ rounded : ℚ, payload.toRat? = some rounded ∧
      |count value payloadUnit - rounded| ≤ 1 / 2 := by
  obtain ⟨rounded, decoded, error⟩ := encodeRne_halfUlp encoded
  exact ⟨rounded, decoded, error.trans (div_le_div_of_nonneg_right (ulp_le_one bounded) (by decide))⟩

end Silmaril.Numeric.UnixRepresentation.Binary64
