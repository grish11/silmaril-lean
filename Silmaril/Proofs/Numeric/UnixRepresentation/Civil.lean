module

public import Silmaril.Numeric.UnixRepresentation.Defs
import Silmaril.Numeric.Gregorian.Thms

public section

namespace Silmaril.Proofs.Numeric.UnixRepresentation

open Silmaril.Numeric.Timestamp
open Silmaril.Numeric.Gregorian
open Silmaril.Numeric.UnixRepresentation

variable {kind : Kind}

theorem toTicks_ofTicks {unit : TickUnit} (value : Ticks kind unit) :
    (Timespec.ofTicks value).toTicks = value.denote := by
  dsimp only [Timespec.toTicks, Timespec.ofTicks, Ticks.denote]
  congr 1
  generalize value.ticks * unit.nanosecondsPerTick = ticks
  have h := Int.emod_add_ediv_mul ticks 1000000000
  omega

theorem ofTicks_toTicks (value : Timespec kind) : Timespec.ofTicks value.toTicks = value := by
  rcases value with ⟨seconds, ⟨nanos, bound⟩⟩
  apply Timespec.ext
  · simp only [Timespec.ofTicks, Timespec.toTicks, Ticks.denote,
      TickUnit.nanosecondsPerTick, Int.mul_one]
    omega
  · apply Fin.ext
    simp only [Timespec.ofTicks, Timespec.toTicks, Ticks.denote,
      TickUnit.nanosecondsPerTick, Int.mul_one]
    omega

theorem civil_encode_decode (value : Timespec kind) :
    (CivilTime.ofTimespec value).toTimespec? kind = some value := by
  rcases value with ⟨seconds, nanos⟩
  have bounds : (seconds % 86400 / 3600).toNat < 24 ∧
      (seconds % 86400 / 60 % 60).toNat < 60 ∧ (seconds % 86400 % 60).toNat < 60 := by
    omega
  have valid : (CivilTime.ofTimespec (⟨seconds, nanos⟩ : Timespec kind)).hour < 24 ∧
      (CivilTime.ofTimespec (⟨seconds, nanos⟩ : Timespec kind)).minute < 60 ∧
      (CivilTime.ofTimespec (⟨seconds, nanos⟩ : Timespec kind)).second < 60 := bounds
  have date := CivilDate.toEpochDay?_ofEpochDay (seconds / 86400)
  change (CivilTime.ofTimespec (⟨seconds, nanos⟩ : Timespec kind)).date.toEpochDay? =
    some (seconds / 86400) at date
  simp only [CivilTime.toTimespec?, date, ite_eq_left valid]
  congr 2
  dsimp [CivilTime.ofTimespec]
  omega

theorem civil_decode_encode {civil : CivilTime} {value : Timespec kind}
    (h : civil.toTimespec? kind = some value) : CivilTime.ofTimespec value = civil := by
  rcases civil with ⟨date, hour, minute, second, nanos⟩
  unfold CivilTime.toTimespec? at h
  cases day : date.toEpochDay? with
  | none => simp [day] at h
  | some dayCount =>
    simp only [day] at h
    split at h
    next bounds =>
      obtain ⟨hh, hm, hs⟩ := bounds
      cases Option.some.inj h
      have splitDay : (dayCount * 86400 + (hour : Int) * 3600 + (minute : Int) * 60 +
        (second : Int)) / 86400 = dayCount := by omega
      apply CivilTime.ext
      · simpa only [CivilTime.ofTimespec, splitDay] using CivilDate.ofEpochDay_toEpochDay? day
      · change ((dayCount * 86400 + (hour : Int) * 3600 + (minute : Int) * 60 +
          (second : Int)) % 86400 / 3600).toNat = hour
        omega
      · change ((dayCount * 86400 + (hour : Int) * 3600 + (minute : Int) * 60 +
          (second : Int)) % 86400 / 60 % 60).toNat = minute
        omega
      · change ((dayCount * 86400 + (hour : Int) * 3600 + (minute : Int) * 60 +
          (second : Int)) % 86400 % 60).toNat = second
        omega
      · rfl
    next => contradiction

theorem civil_ofTicks_toTicks? {unit : TickUnit} {civil : CivilTime} {value : Ticks kind unit}
    (h : civil.toTicks? kind = some value.denote) : CivilTime.ofTicks value = civil := by
  unfold CivilTime.toTicks? at h
  cases hc : civil.toTimespec? kind with
  | none => simp [hc] at h
  | some time =>
    have ht : time.toTicks = value.denote := by simpa [hc] using h
    have same : Timespec.ofTicks value = time := by
      rw [← ofTicks_toTicks time, ht]
      simp [Timespec.ofTicks, Ticks.denote, TickUnit.nanosecondsPerTick]
    unfold CivilTime.ofTicks
    rw [same]
    exact civil_decode_encode hc

end Silmaril.Proofs.Numeric.UnixRepresentation
