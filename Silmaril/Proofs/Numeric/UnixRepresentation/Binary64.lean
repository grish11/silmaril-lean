module

public import Silmaril.Numeric.UnixRepresentation.Binary64.Defs
import Silmaril.Numeric.Ieee754.SignedRationalProperties
import Silmaril.Numeric.Ieee754.ConversionCorrectness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.Proofs.Numeric.UnixRepresentation.Binary64

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.Ieee754 hiding decode
open Silmaril.Numeric.UnixRepresentation (TickRounding)
open Silmaril.Numeric.UnixRepresentation.Binary64
open RationalRounding Binary64Signs

variable {kind : Kind} {source target payloadUnit : TickUnit}

private theorem finite_iff (bits : UInt64) :
    (F64.ofBits bits).IsFinite ↔ (magnitudeBits bits).toNat < limit := by
  unfold F64.IsFinite
  change (decode64 bits.toNat).exponent ≠ _ ↔ _
  rw [exponent_magnitude]
  have bound := magnitudeBits_lt bits
  norm_num [binary64ExponentBits, maxExponentField, limit] at bound ⊢
  omega

private theorem toRat_none_iff (payload : F64) :
    payload.toRat? = none ↔ ¬payload.IsFinite := by
  unfold F64.toRat? F64.IsFinite value64? finiteValue
  by_cases h : (decode64 payload.bits.toNat).exponent = maxExponentField binary64ExponentBits
  · simp [h]
  · simp only [beq_eq_false_iff_ne.mpr h, Bool.false_eq_true, ↓reduceIte]
    split <;> simp [h]

private theorem finite_of_toRat_some {payload : F64} {q : ℚ}
    (decoded : payload.toRat? = some q) : payload.IsFinite := by
  by_contra h
  have missing := (toRat_none_iff payload).mpr h
  rw [decoded] at missing
  contradiction

private theorem toRat_of_finite (bits : UInt64)
    (finite : (magnitudeBits bits).toNat < limit) :
    (F64.ofBits bits).toRat? = some (Decimal.rational bits) := by
  cases h : (F64.ofBits bits).toRat? with
  | none => exact False.elim (toRat_none_iff _ |>.mp h ((finite_iff bits).mpr finite))
  | some q => simp only [Decimal.rational, Conformance.value?_model_unpack64, h, Option.getD_some]

theorem decode_eq_nonfinite_iff (payload : F64) (kind : Kind) (payloadUnit target : TickUnit)
    (rounding : TickRounding) :
    decode kind payload payloadUnit target rounding = .error .nonfinite ↔ ¬payload.IsFinite := by
  rw [← toRat_none_iff]
  unfold decode decodeCount?
  cases payload.toRat? <;> cases rounding <;> simp
  split <;> simp

theorem decode_exact_eq_ok_iff {payload : F64} {result : Ticks kind target} :
    decode kind payload payloadUnit target .exact = .ok result ↔
      decodeCount? payload payloadUnit target = some (result.ticks : ℚ) := by
  unfold decode
  cases decodeCount? payload payloadUnit target with
  | none => simp
  | some q =>
    change (if (⌊q⌋ : ℚ) = q then Except.ok (⟨⌊q⌋⟩ : Ticks kind target)
      else Except.error Error.precisionLoss) = Except.ok result ↔ some q = some (result.ticks : ℚ)
    constructor
    · intro h
      split at h
      next exactCount =>
        cases Except.ok.inj h
        simp [exactCount]
      next => contradiction
    · intro h
      cases Option.some.inj h
      cases result
      simp [Int.floor_intCast]

theorem decode_floor_bounds {payload : F64} {q : ℚ} {result : Ticks kind target}
    (h : decodeCount? payload payloadUnit target = some q)
    (decoded : decode kind payload payloadUnit target .floor = .ok result) :
    (result.ticks : ℚ) ≤ q ∧ q < (result.ticks : ℚ) + 1 := by
  simp only [decode, h] at decoded
  cases Except.ok.inj decoded
  exact ⟨Int.floor_le q, Int.lt_floor_add_one q⟩

theorem decode_trunc_bounds {payload : F64} {q : ℚ} {result : Ticks kind target}
    (h : decodeCount? payload payloadUnit target = some q)
    (decoded : decode kind payload payloadUnit target .trunc = .ok result) :
    (0 ≤ q → (result.ticks : ℚ) ≤ q ∧ q < (result.ticks : ℚ) + 1) ∧
      (q < 0 → q ≤ (result.ticks : ℚ) ∧ (result.ticks : ℚ) < q + 1) := by
  simp only [decode, h] at decoded
  cases Except.ok.inj decoded
  constructor
  · intro nonnegative
    simp [not_lt_of_ge nonnegative, Int.floor_le, Int.lt_floor_add_one]
  · intro negative
    simp [negative, Int.le_ceil, Int.ceil_lt_add_one]

theorem encodeRne_eq_overflow_iff (value : Ticks kind source) (payloadUnit : TickUnit) :
    encodeRne value payloadUnit = .error .overflow ↔
      overflowThreshold ≤ |count value payloadUnit| := by
  dsimp only [encodeRne]
  split <;> simp_all

private theorem encodeRne_parts {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    let q := count value payloadUnit
    |q| < overflowThreshold ∧ payload = F64.ofBits (roundRational q) := by
  dsimp only [encodeRne] at encoded
  split at encoded
  · contradiction
  · exact ⟨lt_of_not_ge ‹_›, (Except.ok.inj encoded).symm⟩

private theorem roundRational_parts (q : ℚ) (below : |q| < overflowThreshold) :
    (magnitudeBits (roundRational q)).toNat < limit ∧
      AdjacentRounding.NearestEven magnitude |q| (magnitudeBits (roundRational q)).toNat :=
  roundSigned_nearestEven _ _ (abs_nonneg q) below

theorem encodeRne_finite_nearestEven {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    payload.IsFinite ∧
      AdjacentRounding.NearestEven magnitude |count value payloadUnit|
        (magnitudeBits payload.bits).toNat := by
  obtain ⟨below, rfl⟩ := encodeRne_parts encoded
  obtain ⟨finite, rne⟩ := roundRational_parts (count value payloadUnit) below
  exact ⟨(finite_iff _).mpr finite, rne⟩

private theorem signed_abs (q : ℚ) : signed (decide (q < 0)) |q| = q := by
  by_cases h : q < 0
  · simp [signed, h, abs_of_neg h]
  · simp [signed, h, abs_of_nonneg (le_of_not_gt h)]

theorem encodeRne_signBit {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    payload.signBit = decide (count value payloadUnit < 0) := by
  obtain ⟨_, rfl⟩ := encodeRne_parts encoded
  exact signBit_roundSigned _ _

private theorem zero_toRat (negative : Bool) :
    (F64.ofBits (if negative then 0x8000000000000000 else 0)).toRat? = some 0 := by
  cases negative <;>
    norm_num [F64.toRat?, F64.ofBits, value64?, decode64, Silmaril.Numeric.Ieee754.decode, field,
      finiteValue, signed, binary64Bias, binary64ExponentBits, binary64SignificandBits,
      maxExponentField, UInt64.toNat_ofNat']

theorem decode_signedZero (negative : Bool) (kind : Kind) (payloadUnit target : TickUnit)
    (rounding : TickRounding) :
    decode kind (F64.ofBits (if negative then 0x8000000000000000 else 0))
      payloadUnit target rounding = .ok ⟨0⟩ := by
  cases rounding <;> simp [decode, decodeCount?, zero_toRat, Int.floor_zero]

theorem encodeExact_eq_ok_iff {value : Ticks kind source} {payload : F64} :
    encodeExact value payloadUnit = .ok payload ↔
      encodeRne value payloadUnit = .ok payload ∧ payload.toRat? = some (count value payloadUnit) := by
  unfold encodeExact
  cases encodeRne value payloadUnit with
  | error => simp
  | ok rounded =>
    by_cases h : rounded.toRat? = some (count value payloadUnit)
    · simp only [ite_eq_left h, Except.ok.injEq]
      exact ⟨fun eq => ⟨eq, eq ▸ h⟩, And.left⟩
    · simp only [ite_eq_right h, reduceCtorEq, Except.ok.injEq, false_iff]
      rintro ⟨rfl, same⟩
      exact h same

theorem encodeExact_zero (kind : Kind) (source payloadUnit : TickUnit) :
    encodeExact (⟨0⟩ : Ticks kind source) payloadUnit = .ok (F64.ofBits 0) := by
  have countZero : count (⟨0⟩ : Ticks kind source) payloadUnit = 0 := by
    simp [count, Ticks.denote]
  have decodeZero : (F64.ofBits 0).toRat? = some 0 := zero_toRat false
  apply encodeExact_eq_ok_iff.mpr
  simp [encodeRne, countZero, overflowThreshold_pos.not_ge, roundRational, decodeZero]

theorem encodeRne_nearest {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    ∃ rounded : ℚ, payload.toRat? = some rounded ∧
      ∀ (candidate : F64) (exact : ℚ), candidate.toRat? = some exact →
        |count value payloadUnit - rounded| ≤ |count value payloadUnit - exact| := by
  obtain ⟨below, rfl⟩ := encodeRne_parts encoded
  let q := count value payloadUnit
  have finite := (roundRational_parts q below).1
  refine ⟨_, toRat_of_finite _ finite, ?_⟩
  rintro ⟨bits⟩ exact decoded
  have bound := (finite_iff bits).mp (finite_of_toRat_some decoded)
  have nearest := roundSigned_nearestFinite (decide (q < 0)) |q| (abs_nonneg q) below bits
    (Nat.le_pred_of_lt bound)
  have rational : Decimal.rational bits = exact := by
    simp only [Decimal.rational, Conformance.value?_model_unpack64]
    change (F64.ofBits bits).toRat? = some exact at decoded
    rw [decoded, Option.getD_some]
  rw [signed_abs, rational] at nearest
  exact nearest

theorem encodeExact_roundtrip {value : Ticks kind source} {payload : F64}
    (encoded : encodeExact value payloadUnit = .ok payload) :
    decode kind payload payloadUnit source .exact = .ok value := by
  have exactValue := (encodeExact_eq_ok_iff.mp encoded).2
  have scaleSource : (source.nanosecondsPerTick : ℚ) ≠ 0 := by cases source <;> decide
  have scaleDest : (payloadUnit.nanosecondsPerTick : ℚ) ≠ 0 := by cases payloadUnit <;> decide
  apply decode_exact_eq_ok_iff.mpr
  simp only [decodeCount?, exactValue, Option.map_some, count, Ticks.denote, Int.cast_mul,
    Option.some.injEq]
  field_simp

theorem encodeExact_exists_iff {value : Ticks kind source} :
    (∃ payload, encodeExact value payloadUnit = .ok payload) ↔
      |count value payloadUnit| < overflowThreshold ∧
        ∃ candidate : F64, candidate.toRat? = some (count value payloadUnit) := by
  unfold encodeExact
  cases h : encodeRne value payloadUnit with
  | error error =>
    have notBelow : ¬|count value payloadUnit| < overflowThreshold := by
      intro below
      simp [encodeRne, not_le_of_gt below] at h
    simp [notBelow]
  | ok payload =>
    obtain ⟨below, _⟩ := encodeRne_parts h
    obtain ⟨q, decoded, nearest⟩ := encodeRne_nearest h
    simp only [below, true_and]
    constructor
    · rintro ⟨result, encoded⟩
      split at encoded
      next same => exact ⟨payload, same⟩
      next => contradiction
    · rintro ⟨candidate, exactValue⟩
      have error := nearest candidate _ exactValue
      rw [sub_self, abs_zero, abs_nonpos_iff, sub_eq_zero] at error
      exact ⟨payload, by simp [decoded, error]⟩

private theorem finite_abs_lt_overflow {payload : F64} {q : ℚ}
    (decoded : payload.toRat? = some q) : |q| < overflowThreshold := by
  rcases payload with ⟨bits⟩
  change (F64.ofBits bits).toRat? = some q at decoded
  have bound := Nat.le_pred_of_lt ((finite_iff bits).mp (finite_of_toRat_some decoded))
  have value : Decimal.rational bits = q := by
    simp only [Decimal.rational, Conformance.value?_model_unpack64, decoded, Option.getD_some]
  rw [← value, rational_signed_magnitude, Decimal.rational_eq_binaryMagnitude _ bound]
  have nonnegative := BinaryMagnitude.value_nonneg 52 1023 (magnitudeBits bits).toNat
  have magLe := magnitude_strictMono.monotone bound
  cases (F64.ofBits bits).signBit <;>
    simpa only [magnitude, signed, Bool.false_eq_true, ↓reduceIte, abs_neg,
      abs_of_nonneg nonnegative] using
      magLe.trans_lt maxFinite_lt_overflowThreshold

theorem decodeExact_roundtrip {payload : F64} {value : Ticks kind target}
    (decoded : decode kind payload payloadUnit target .exact = .ok value) :
    ∃ result, encodeExact value payloadUnit = .ok result ∧ result.toRat? = payload.toRat? := by
  have h := decode_exact_eq_ok_iff.mp decoded
  unfold decodeCount? at h
  cases fin : payload.toRat? with
  | none => simp [fin] at h
  | some q =>
    have scaleSrc : (target.nanosecondsPerTick : ℚ) ≠ 0 := by cases target <;> decide
    have scaleDest : (payloadUnit.nanosecondsPerTick : ℚ) ≠ 0 := by cases payloadUnit <;> decide
    have scaled : q * (payloadUnit.nanosecondsPerTick : ℚ) / (target.nanosecondsPerTick : ℚ) =
        (value.ticks : ℚ) := by simpa [fin] using h
    have exactCount : count value payloadUnit = q := by
      simp only [count, Ticks.denote, Int.cast_mul, ← scaled]
      field_simp
    obtain ⟨result, encoded⟩ := encodeExact_exists_iff.mpr
      ⟨exactCount ▸ finite_abs_lt_overflow fin, payload, exactCount ▸ fin⟩
    exact ⟨result, encoded, (encodeExact_eq_ok_iff.mp encoded).2.trans (congrArg some exactCount)⟩

theorem encodeRne_halfUlp {value : Ticks kind source} {payload : F64}
    (encoded : encodeRne value payloadUnit = .ok payload) :
    ∃ rounded : ℚ, payload.toRat? = some rounded ∧
      |count value payloadUnit - rounded| ≤ ulp (count value payloadUnit) / 2 := by
  obtain ⟨below, rfl⟩ := encodeRne_parts encoded
  let q := count value payloadUnit
  let lower := Bisection.lastLE magnitude |q| 0 limit
  have ⟨finite, rne⟩ := roundRational_parts q below
  obtain ⟨_, left, right⟩ := bracket_spec |q| (abs_nonneg q) below
  refine ⟨_, toRat_of_finite _ finite, ?_⟩
  have posFinite : (roundPositive |q|).toNat ≤ limit - 1 := by
    simpa only [roundRational, magnitudeBits_roundSigned, Nat.pred_eq_sub_one] using
      Nat.le_pred_of_lt finite
  have distance :
      |q - Decimal.rational (roundRational q)| =
        |(|q| - magnitude (magnitudeBits (roundRational q)).toNat)| := by
    conv_lhs => rw [roundRational, rational_roundSigned,
      Decimal.rational_eq_binaryMagnitude _ posFinite]
    rw [roundRational, magnitudeBits_roundSigned]
    change |q - signed (decide (q < 0)) (magnitude (roundPositive |q|).toNat)| = _
    by_cases neg : q < 0
    · simp only [signed, neg, decide_true, ↓reduceIte]
      rw [abs_of_neg neg, ← abs_neg (q - -magnitude (roundPositive (-q)).toNat)]
      congr 1
      linarith
    · simp [signed, neg, abs_of_nonneg (le_of_not_gt neg)]
  change |q - Decimal.rational (roundRational q)| ≤ ulp q / 2
  rw [distance]
  have lowError := rne.1 lower
  have highError := rne.1 (lower + 1)
  rw [abs_of_nonneg (sub_nonneg.mpr left)] at lowError
  rw [abs_of_nonpos (sub_nonpos.mpr right.le)] at highError
  have step : magnitude (lower + 1) = magnitude lower + ulp q :=
    BinaryMagnitude.value_succ 52 1023 lower
  linarith

private theorem magnitude_at_two_pow53 :
    magnitude 0x4340000000000000 = (2 : ℚ) ^ (53 : Nat) := by
  norm_num [magnitude, BinaryMagnitude.value, BinaryMagnitude.spacing,
    BinaryMagnitude.significand, BinaryMagnitude.radix]

private theorem two_pow53_below_overflow : (2 : ℚ) ^ (53 : Nat) < overflowThreshold := by
  rw [← magnitude_at_two_pow53]
  exact (magnitude_strictMono.monotone (show 0x4340000000000000 ≤ limit - 1 by decide)).trans_lt
    maxFinite_lt_overflowThreshold

theorem ulp_le_one {q : ℚ} (bounded : |q| < (2 : ℚ) ^ (53 : Nat)) : ulp q ≤ 1 := by
  let lower := Bisection.lastLE magnitude |q| 0 limit
  have below := bounded.trans two_pow53_below_overflow
  have left : magnitude lower ≤ |q| := (bracket_spec |q| (abs_nonneg q) below).2.1
  have indexBound : lower < 0x4340000000000000 := by
    apply magnitude_strictMono.lt_iff_lt.mp
    exact left.trans_lt (magnitude_at_two_pow53 ▸ bounded)
  change (2 : ℚ) ^ ((max (lower / BinaryMagnitude.radix 52) 1 : Nat) - (1023 : Int) - 52) ≤ 1
  rw [← zpow_zero (2 : ℚ)]
  apply zpow_le_zpow_right₀ (by decide)
  norm_num [BinaryMagnitude.radix] at indexBound ⊢
  omega

open Float.Model Float.Model.UnpackedFloat Conformance in
private theorem representableDyadic (sign : Sign) (n : Nat) (hn : 0 < n) (bounded : n < 2 ^ 53)
    (e : Int) (lower : 0 ≤ e) (upper : e ≤ 1) :
    ∃ f : F64, f.toRat? = some (dyadic (sign.apply n) e) := by
  let input : UnpackedFloat := .finite sign n e hn
  let bits := Rounding.packRounded .binary64 .nearestTiesToEven input
  have log := (Nat.log2_lt (Nat.ne_of_gt hn)).mpr bounded
  have fits : Format.binary64.targetExponent (totalExponent n e) ≤ e := by
    norm_num [Format.targetExponent, totalExponent, Format.minExponent, Format.mantissaBits,
      Format.binary64]
    omega
  have noOverflow : NoExponentOverflow .binary64
      (Rounding.roundUnpacked .binary64 .nearestTiesToEven input) := by
    unfold input
    rw [roundUnpacked_finite_of_target_le _ _ _ _ _ _ fits]
    change (Format.binary64.targetExponent (totalExponent n e) + 1023 + 52).toNat < 2047
    omega
  refine ⟨F64.ofBits (UInt64.ofBitVec bits), ?_⟩
  rw [show (F64.ofBits (UInt64.ofBitVec bits)).toRat? =
      value? (UnpackedFloat.unpack .binary64 bits) from (value?_unpack .binary64 bits).symm,
    unpack_packRounded _ _ _ noOverflow,
    value?_roundUnpacked_of_target_le _ _ _ _ _ _ fits]
  rfl

private theorem representableNat (negative : Bool) (n : Nat) (bounded : n ≤ 2 ^ 53) :
    ∃ f : F64, f.toRat? = some (signed negative (n : ℚ)) := by
  by_cases zero : n = 0
  · subst n
    refine ⟨F64.ofBits 0, ?_⟩
    have h : (F64.ofBits 0).toRat? = some 0 := zero_toRat false
    cases negative <;> simpa [signed] using h
  let sign : Float.Model.UnpackedFloat.Sign := if negative then .negative else .positive
  by_cases edge : n = 2 ^ 53
  · obtain ⟨f, hf⟩ := representableDyadic sign (2 ^ 52) (by decide) (by decide) 1 (by decide) (by decide)
    refine ⟨f, hf.trans ?_⟩
    cases negative <;> norm_num [edge, sign, signed, Conformance.dyadic, Float.Model.UnpackedFloat.Sign.apply]
  · obtain ⟨f, hf⟩ := representableDyadic sign n (Nat.pos_of_ne_zero zero)
      (lt_of_le_of_ne bounded edge) 0 (by decide) (by decide)
    refine ⟨f, hf.trans ?_⟩
    cases negative <;> simp [sign, signed, Conformance.dyadic, Float.Model.UnpackedFloat.Sign.apply]

theorem encodeExact_of_int {value : Ticks kind source} {n : Int}
    (integer : count value payloadUnit = (n : ℚ)) (bounded : n.natAbs ≤ 2 ^ 53) :
    ∃ payload, encodeExact value payloadUnit = .ok payload := by
  apply encodeExact_exists_iff.mpr
  rw [integer]
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · have hm : m ≤ 2 ^ 53 := bounded
    refine ⟨?_, ?_⟩
    · rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg m)]
      exact (by exact_mod_cast hm : (m : ℚ) ≤ 2 ^ (53 : Nat)).trans_lt two_pow53_below_overflow
    · simpa [signed] using representableNat false m hm
  · have hm : m ≤ 2 ^ 53 := by simpa using bounded
    refine ⟨?_, ?_⟩
    · rw [Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
      exact (by exact_mod_cast hm : (m : ℚ) ≤ 2 ^ (53 : Nat)).trans_lt two_pow53_below_overflow
    · simpa [signed] using representableNat true m hm

end Silmaril.Proofs.Numeric.UnixRepresentation.Binary64
