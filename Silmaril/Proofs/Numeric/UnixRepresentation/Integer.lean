module

public import Silmaril.Numeric.UnixRepresentation.Defs
import Silmaril.Numeric.Timestamp.Thms

public section

namespace Silmaril.Proofs.Numeric.UnixRepresentation

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.UnixRepresentation

variable {kind : Kind} {source target : TickUnit}

theorem scale_pos (unit : TickUnit) : 0 < unit.nanosecondsPerTick := by
  cases unit <;> decide

theorem quantize_floor {value : Ticks kind source} {rounded : Ticks kind target}
    (h : quantize value target .floor = some rounded) :
    0 ≤ value.denote.ticks - rounded.denote.ticks ∧
      value.denote.ticks - rounded.denote.ticks < target.nanosecondsPerTick := by
  cases Option.some.inj h.symm
  dsimp only [Ticks.denote]
  have positive := scale_pos target
  generalize value.ticks * source.nanosecondsPerTick = n
  generalize target.nanosecondsPerTick = scale at positive ⊢
  have remainder := Int.emod_add_ediv_mul n scale
  have lower := Int.emod_nonneg n (Int.ne_of_gt positive)
  have upper := Int.emod_lt_of_pos n positive
  change 0 ≤ n - n / scale * scale ∧ n - n / scale * scale < scale
  omega

theorem quantize_trunc {value : Ticks kind source} {rounded : Ticks kind target}
    (h : quantize value target .trunc = some rounded) :
    let error := value.denote.ticks - rounded.denote.ticks;
    -target.nanosecondsPerTick < error ∧ error < target.nanosecondsPerTick ∧
      (0 ≤ value.denote.ticks → 0 ≤ error) ∧ (value.denote.ticks ≤ 0 → error ≤ 0) := by
  cases Option.some.inj h.symm
  dsimp only [Ticks.denote]
  have positive := scale_pos target
  generalize value.ticks * source.nanosecondsPerTick = n
  generalize target.nanosecondsPerTick = scale at positive ⊢
  change -scale < n - n.tdiv scale * scale ∧ n - n.tdiv scale * scale < scale ∧
    (0 ≤ n → 0 ≤ n - n.tdiv scale * scale) ∧ (n ≤ 0 → n - n.tdiv scale * scale ≤ 0)
  have remainder := Int.tmod_add_tdiv_mul n scale
  have lower := Int.lt_tmod_of_pos n positive
  have upper := Int.tmod_lt_of_pos n positive
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro hn
    have sign := Int.tmod_nonneg scale hn
    omega
  · intro hn
    have sign := Int.tmod_nonneg scale (show 0 ≤ -n by omega)
    rw [Int.neg_tmod] at sign
    omega

namespace WordFormat

variable {format : WordFormat}

theorem toInt_inRange (payload : format.Payload) : format.InRange (format.toInt payload) := by
  cases format with
  | int32 => exact ⟨payload.minValue_le_toInt, payload.toInt_le⟩
  | int64 => exact ⟨payload.minValue_le_toInt, payload.toInt_le⟩
  | uint64 =>
    have bound : payload.toNat < UInt64.size := payload.toNat_lt
    change 0 ≤ (payload.toNat : Int) ∧ (payload.toNat : Int) ≤ (UInt64.size : Int) - 1
    exact ⟨Int.natCast_nonneg _, by omega⟩

theorem toInt_ofInt {count : Int} (h : format.InRange count) :
    format.toInt (format.ofInt count h) = count := by
  cases format with
  | int32 => exact Int32.toInt_ofIntLE (h₁ := h.1) (h₂ := h.2)
  | int64 => exact Int64.toInt_ofIntLE (h₁ := h.1) (h₂ := h.2)
  | uint64 =>
    have nonnegative : 0 ≤ count := h.1
    simpa only [Silmaril.Numeric.UnixRepresentation.WordFormat.ofInt,
      Silmaril.Numeric.UnixRepresentation.WordFormat.toInt, UInt64.toNat_ofNatLT] using
      Int.toNat_of_nonneg nonnegative

private theorem toInt_injective {left right : format.Payload}
    (h : format.toInt left = format.toInt right) : left = right := by
  cases format with
  | int32 => exact Int32.toInt.inj h
  | int64 => exact Int64.toInt.inj h
  | uint64 => exact UInt64.toNat_inj.mp (Int.ofNat.inj h)

theorem encode_eq_ok_iff {value : Ticks kind source} {rounding : TickRounding}
    {payload : format.Payload} :
    format.encode value target rounding = .ok payload ↔
      quantize value target rounding = some (format.decode kind target payload) := by
  unfold Silmaril.Numeric.UnixRepresentation.WordFormat.encode
  cases quantize value target rounding with
  | none => simp
  | some count =>
    change (if h : format.InRange count.ticks then Except.ok (format.ofInt count.ticks h)
      else Except.error ConversionError.outOfRange) = Except.ok payload ↔ some count = some (format.decode kind target payload)
    constructor
    · intro h
      split at h
      next bounds =>
        cases Except.ok.inj h
        cases count
        simp [Silmaril.Numeric.UnixRepresentation.WordFormat.decode, toInt_ofInt]
      next => contradiction
    · intro h
      cases Option.some.inj h
      have range : format.InRange (format.decode kind target payload).ticks :=
        toInt_inRange payload
      rw [dite_eq_left range]
      exact congrArg Except.ok (toInt_injective (toInt_ofInt (toInt_inRange payload)))

theorem encode_exists_iff {value : Ticks kind source} {rounding : TickRounding} :
    (∃ payload, format.encode value target rounding = .ok payload) ↔
      ∃ count : Ticks kind target, quantize value target rounding = some count ∧
        format.InRange count.ticks := by
  constructor
  · rintro ⟨payload, h⟩
    exact ⟨_, encode_eq_ok_iff.mp h, toInt_inRange payload⟩
  · rintro ⟨count, h, bounds⟩
    exact ⟨format.ofInt count.ticks bounds, by
      simp [Silmaril.Numeric.UnixRepresentation.WordFormat.encode, h, bounds]⟩

theorem encode_exact_eq_ok_iff {value : Ticks kind source} {payload : format.Payload} :
    format.encode value target .exact = .ok payload ↔
      value.denote = (format.decode kind target payload).denote :=
  encode_eq_ok_iff.trans Ticks.rescale_eq_some_iff

theorem encode_exact_eq_precisionLoss_iff {value : Ticks kind source} :
    format.encode value target .exact = .error .precisionLoss ↔
      value.denote.ticks % target.nanosecondsPerTick ≠ 0 := by
  unfold Silmaril.Numeric.UnixRepresentation.WordFormat.encode quantize Ticks.rescale
  by_cases h : value.denote.ticks % target.nanosecondsPerTick = 0
  · by_cases bounds : format.InRange (value.denote.ticks / target.nanosecondsPerTick) <;>
      simp [h, bounds]
  · simp [h]

theorem encode_eq_outOfRange_iff {value : Ticks kind source} {rounding : TickRounding} :
    format.encode value target rounding = .error .outOfRange ↔
      ∃ count : Ticks kind target, quantize value target rounding = some count ∧
        ¬ format.InRange count.ticks := by
  unfold Silmaril.Numeric.UnixRepresentation.WordFormat.encode
  cases quantize value target rounding with
  | none => simp
  | some count => by_cases bounds : format.InRange count.ticks <;> simp [bounds]

end WordFormat

end Silmaril.Proofs.Numeric.UnixRepresentation
