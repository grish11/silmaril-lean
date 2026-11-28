module

public import Silmaril.Formats.Parquet.Int96.Defs
import Silmaril.Prelude.Bytes.Digits.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Int96

open Silmaril.Formats.Parquet.Int96

theorem encode_length (value : Payload) : value.encode.length = 12 := by
  rw [Payload.encode, List.length_append, KBytes.length_unpack, KBytes.length_unpack]

theorem decode_encode (value : Payload) : Payload.decode? value.encode = some value := by
  have nanosFit : value.nanosecondOfDay.val < 256 ^ 8 :=
    Nat.lt_trans value.nanosecondOfDay.isLt (by decide)
  have dayFit : value.julianDay.toUInt32.toNat < 256 ^ 4 :=
    value.julianDay.toUInt32.toNat_lt
  rw [Payload.decode?, ite_eq_left (encode_length value)]
  simp only [Payload.encode,
    List.take_left' (KBytes.length_unpack 8 _), List.drop_left' (KBytes.length_unpack 8 _),
    KBytes.leVal_unpack, Nat.mod_eq_of_lt nanosFit, Nat.mod_eq_of_lt dayFit,
    dite_eq_left value.nanosecondOfDay.isLt, UInt32.ofNat_toNat, Int32.toInt32_toUInt32]

theorem encode_of_decode {bytes : List UInt8} {value : Payload}
    (h : Payload.decode? bytes = some value) : value.encode = bytes := by
  unfold Payload.decode? at h
  split at h
  next length =>
    dsimp only at h
    split at h
    next valid =>
      cases Option.some.inj h
      have takeBytes := KBytes.unpack_leVal (bytes.take 8)
      have dropBytes := KBytes.unpack_leVal (bytes.drop 8)
      simp only [List.length_take, List.length_drop, length] at takeBytes dropBytes
      change KBytes.unpack 8 (KBytes.leVal (bytes.take 8)) = bytes.take 8 at takeBytes
      change KBytes.unpack 4 (KBytes.leVal (bytes.drop 8)) = bytes.drop 8 at dropBytes
      have dayMod : KBytes.leVal (bytes.drop 8) % (256 ^ 4) = KBytes.leVal (bytes.drop 8) := by
        rw [← KBytes.leVal_unpack, dropBytes]
      simp only [Payload.encode, UInt32.toUInt32_toInt32, UInt32.toNat_ofNat']
      change KBytes.unpack 8 (KBytes.leVal (bytes.take 8)) ++
        KBytes.unpack 4 (KBytes.leVal (bytes.drop 8) % (256 ^ 4)) = bytes
      rw [dayMod, takeBytes, dropBytes, List.take_append_drop]
    next => contradiction
  next => contradiction

theorem decode_eq_none_iff (bytes : List UInt8) : Payload.decode? bytes = none ↔
    bytes.length ≠ 12 ∨ nanosecondsPerDay ≤ KBytes.leVal (bytes.take 8) := by
  by_cases length : bytes.length = 12
  · by_cases nanos : KBytes.leVal (bytes.take 8) < nanosecondsPerDay
    · simp [Payload.decode?, length, nanos]
    · simpa [Payload.decode?, length, nanos] using Nat.le_of_not_gt nanos
  · simp [Payload.decode?, length]

end Silmaril.Proofs.Formats.Parquet.Int96
