module

public import Silmaril.Formats.Sqlite.Varint.Defs

public section
namespace Silmaril.Proofs.Formats.Sqlite.Varint.Nine

open Silmaril.Formats Silmaril.Formats.Sqlite

private def digit (value index : Nat) : UInt8 :=
  UInt8.ofNat (value / 2 ^ (8 + 7 * (7 - index)) % 128 + 128)

private theorem digit_nat (value index : Nat) :
    (digit value index).toNat = value / 2 ^ (8 + 7 * (7 - index)) % 128 + 128 := by
  apply UInt8.toNat_ofNat_of_lt'
  have := Nat.mod_lt (value / 2 ^ (8 + 7 * (7 - index))) (by decide : 0 < 128)
  change _ < 256
  omega

private theorem read_cont (view : File.View) (fuel offset acc value index : Nat)
    (byte : view.get? offset = some (digit value index)) :
    Varint.readAux? view (fuel + 2) offset acc =
      Varint.readAux? view (fuel + 1) (offset + 1) (acc * 128 + value / 2 ^ (8 + 7 * (7 - index)) % 128) := by
  rw [Varint.readAux?, byte]
  change (if (digit value index).toNat < 128 then
      some (acc * 128 + (digit value index).toNat % 128, offset + 1)
    else Varint.readAux? view (fuel + 1) (offset + 1) (acc * 128 + (digit value index).toNat % 128)) = _
  rw [digit_nat, ite_eq_right (by omega)]
  congr 2
  omega

private theorem read_last (view : File.View) (offset acc value : Nat)
    (byte : view.get? offset = some (UInt8.ofNat (value % 256))) :
    Varint.readAux? view 1 offset acc = some (acc * 256 + value % 256, offset + 1) := by
  unfold Varint.readAux?
  rw [byte]
  simp [UInt8.toNat_ofNat']

private theorem encode_list (value : UInt64) (high : 2 ^ 56 ≤ value.toNat) :
    (Varint.encode value).toList =
      (List.range 8).map (digit value.toNat) ++ [UInt8.ofNat (value.toNat % 256)] := by
  unfold Varint.encode
  rw [ite_eq_right (Nat.not_lt.mpr high), Bytes.toList_ofList]
  rfl

private theorem recover_digit (n scale : Nat) :
    n / (scale * 128) * 128 + n / scale % 128 = n / scale := by
  rw [← Nat.div_div_eq_div_mul, Nat.mul_comm _ 128, Nat.div_add_mod]

theorem read_encode (view : File.View) (offset : Nat) (value : UInt64)
    (high : 2 ^ 56 ≤ value.toNat)
    (bytes : ∀ i, i < 9 → view.get? (offset + i) = (Varint.encode value).toList[i]?) :
    Varint.read? view offset = some (value, offset + 9) := by
  have first (i : Nat) (hi : i < 8) :
      view.get? (offset + i) = some (digit value.toNat i) := by
    rw [bytes i (by omega), encode_list value high, List.getElem?_append_left (by simpa using hi)]
    simp [List.getElem?_range hi]
  have last : view.get? (offset + 8) = some (UInt8.ofNat (value.toNat % 256)) := by
    rw [bytes 8 (by decide), encode_list value high]
    rfl
  have step (fuel i acc : Nat) (hi : i < 8) :
      Varint.readAux? view (fuel + 2) (offset + i) acc =
        Varint.readAux? view (fuel + 1) (offset + (i + 1))
          (acc * 128 + value.toNat / 2 ^ (8 + 7 * (7 - i)) % 128) := by
    rw [← Nat.add_assoc]
    exact read_cont view fuel (offset + i) acc value.toNat i (first i hi)
  have terminal (acc : Nat) :
      Varint.readAux? view 1 (offset + 8) acc =
        some (acc * 256 + value.toNat % 256, offset + 9) :=
    read_last view (offset + 8) acc value.toNat last
  change (Varint.readAux? view 9 (offset + 0) 0).map _ = _
  rw [step 7 0 0 (by decide), step 6 1 _ (by decide), step 5 2 _ (by decide),
      step 4 3 _ (by decide), step 3 4 _ (by decide), step 2 5 _ (by decide),
      step 1 6 _ (by decide), step 0 7 _ (by decide), terminal]
  simp only [Nat.zero_mul, Nat.zero_add, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
  have convert (n : Nat) (same : n = value.toNat) : UInt64.ofNat n = value := by
    rw [same, UInt64.ofNat_toNat]
  apply convert
  have top : value.toNat / 2 ^ (8 + 7 * (7 - 0)) % 128 = value.toNat / 2 ^ (8 + 7 * (7 - 0)) := by
    apply Nat.mod_eq_of_lt
    exact (Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 57)).mpr value.toNat_lt
  have carry (i j : Nat) (hi : i < 7) (next : j = i + 1) :
      value.toNat / 2 ^ (8 + 7 * (7 - i)) * 128 + value.toNat / 2 ^ (8 + 7 * (7 - j)) % 128 =
        value.toNat / 2 ^ (8 + 7 * (7 - j)) := by
    have exp : 8 + 7 * (7 - i) = (8 + 7 * (7 - j)) + 7 := by omega
    rw [exp, Nat.pow_add]
    exact recover_digit value.toNat (2 ^ (8 + 7 * (7 - j)))
  rw [top, carry 0 1 (by decide) rfl, carry 1 2 (by decide) rfl, carry 2 3 (by decide) rfl,
      carry 3 4 (by decide) rfl, carry 4 5 (by decide) rfl, carry 5 6 (by decide) rfl,
      carry 6 7 (by decide) rfl]
  have lastScale : 2 ^ (8 + 7 * (7 - 7)) = 256 := rfl
  rw [lastScale, Nat.mul_comm _ 256, Nat.div_add_mod]


end Silmaril.Proofs.Formats.Sqlite.Varint.Nine
