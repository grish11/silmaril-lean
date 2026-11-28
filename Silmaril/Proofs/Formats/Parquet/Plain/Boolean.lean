module

public import Silmaril.Formats.Parquet.Plain.Defs
import Init.Data.ByteArray.Lemmas
import Init.Data.BitVec.Lemmas
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Plain

open Silmaril.Formats Silmaril.Formats.Parquet.Plain

private theorem booleanIndex {count i : Nat} (hi : i < count) :
    i / 8 < booleanByteCount count := by
  unfold booleanByteCount
  omega

private theorem getByte_toList (source : Bytes) {offset : Nat} (h : offset < source.length) :
    source.toList[offset]? = some (source.data[offset]'h) := by
  have hlist : offset < source.toList.length := by simpa using h
  rw [getElem?_def, dite_eq_left hlist]
  simp only [Bytes.toList, Array.getElem_toList]
  rfl

public theorem decodeBoolean_ok_iff {count : Nat} {source : Bytes} {values : List Bool} :
    decodeBoolean count source = .ok values ↔
      source.length = booleanByteCount count ∧ values.length = count ∧
        ∀ i : Nat, (hi : i < values.length) →
          (source.toList[i / 8]?).map (fun byte => byte.toNat.testBit (i % 8)) = some values[i] := by
  unfold decodeBoolean
  split
  · rename_i sized
    constructor
    · intro h
      cases h
      refine ⟨sized, List.length_ofFn, fun i hi => ?_⟩
      have hcount : i < count := by simpa using hi
      rw [List.getElem_ofFn]
      rw [getByte_toList source (sized ▸ booleanIndex hcount)]
      rfl
    · rintro ⟨_, hcount, bit⟩
      apply congrArg Except.ok
      apply List.ext_getElem (by simpa using hcount.symm)
      intro i _ hi
      rw [List.getElem_ofFn]
      have hbyte : i / 8 < source.length := sized ▸ booleanIndex (hcount ▸ hi)
      have same := bit i hi
      rw [getByte_toList source hbyte] at same
      exact Option.some.inj same
  · rename_i unsized
    split <;> simp [unsized]

private theorem booleanOctet_bit (values : Array Bool) (octet bit : Nat) (hb : bit < 8) :
    (booleanOctet values octet).toNat.testBit bit =
      values[8 * octet + bit]?.getD false := by
  let chunk := List.ofFn fun (i : Fin 8) => values[8 * octet + i.val]?.getD false
  have hlength : chunk.length = 8 := List.length_ofFn
  have bound : (BitVec.ofBoolListLE chunk).toNat < 256 := by
    calc
      _ < 2 ^ chunk.length := (BitVec.ofBoolListLE chunk).isLt
      _ = 256 := by rw [hlength]
  change ((BitVec.ofBoolListLE chunk).toNat % 256).testBit bit = _
  rw [Nat.mod_eq_of_lt (by exact bound)]
  change (BitVec.ofBoolListLE chunk).getLsbD bit = _
  rw [BitVec.getLsbD_ofBoolListLE]
  have hin : bit < chunk.length := hlength ▸ hb
  simp only [List.getD_eq_getElem?_getD, getElem?_def, dite_eq_left hin, Option.getD_some]
  rw [show chunk[bit] = values[8 * octet + bit]?.getD false by
    unfold chunk
    rw [List.getElem_ofFn]]
  rfl

public theorem encodeBoolean_length (values : List Bool) :
    (encodeBoolean values).length = booleanByteCount values.length := by
  simp [encodeBoolean]

public theorem encodeBoolean_bit (values : List Bool) {octet bit : Nat}
    (ho : octet < booleanByteCount values.length) (hb : bit < 8) :
    ((encodeBoolean values).toList[octet]?).map (fun byte => byte.toNat.testBit bit) =
      some (values[8 * octet + bit]?.getD false) := by
  have hbyte : octet < (encodeBoolean values).toList.length := by
    rwa [Bytes.length_toList, encodeBoolean_length]
  rw [getElem?_def, dite_eq_left hbyte]
  simp [encodeBoolean, List.getElem_ofFn, booleanOctet_bit values.toArray octet bit hb]

public theorem decodeBoolean_encodeBoolean (values : List Bool) :
    decodeBoolean values.length (encodeBoolean values) = .ok values := by
  apply decodeBoolean_ok_iff.mpr
  refine ⟨encodeBoolean_length values, rfl, fun i hi => ?_⟩
  rw [encodeBoolean_bit values (booleanIndex hi) (by omega)]
  have index : 8 * (i / 8) + i % 8 = i := by omega
  rw [index, getElem?_def, dite_eq_left hi]
  rfl

end Silmaril.Proofs.Formats.Parquet.Plain
