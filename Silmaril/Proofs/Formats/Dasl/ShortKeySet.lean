module

public import Silmaril.Formats.Dasl.ShortKeySet.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.ShortKeySet

open Silmaril.Formats.Dasl.ShortKeySet Silmaril.Semantics

theorem unpack_pack {limit : Fin 256} (keys : List (Bytes limit)) {fuel : Nat} (enough : keys.length ≤ fuel) :
    unpack limit fuel (pack keys) = some keys := by
  induction keys generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons key tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have fits : key.val.length ≤ limit.val ∧ key.val.length ≤ (key.val ++ pack tail).length :=
        ⟨key.property, by simp⟩
      simp only [pack, unpack, lengthPrefix, dite_eq_left fits, List.take_left, List.drop_left,
        ih (Nat.le_of_succ_le_succ enough), Option.map_some]

theorem pack_of_unpacked {limit : Fin 256} {raw : List (Fin 256)} {keys : List (Bytes limit)} {fuel : Nat}
    (hit : unpack limit fuel raw = some keys) : pack keys = raw := by
  induction fuel generalizing raw keys with
  | zero =>
    cases raw <;> simp [unpack] at hit
    subst keys
    rfl
  | succ fuel ih =>
    cases raw with
    | nil =>
      simp [unpack] at hit
      subst keys
      rfl
    | cons length tail =>
      by_cases fits : length.val ≤ limit.val ∧ length.val ≤ tail.length
      · rw [unpack, dite_eq_left fits] at hit
        obtain ⟨rest, decodedRest, rfl⟩ := Option.map_eq_some_iff.mp hit
        let next : Bytes limit := ⟨tail.take length.val, (List.length_take_le _ _).trans fits.1⟩
        have prefixEq : lengthPrefix next = length := Fin.ext (by simp [next, lengthPrefix, List.length_take, fits.2])
        change lengthPrefix next :: (tail.take length.val ++ pack rest) = length :: tail
        rw [prefixEq, ih decodedRest, List.take_append_drop]
      · rw [unpack, dite_eq_right fits] at hit
        contradiction

theorem octets_recovers {limit : Fin 256} (key : Text limit) : Text.fromOctets? key.octets = some key := by
  have bytes : (key.octets.val.map UInt8.ofFin).toByteArray = key.val.toByteArray := by
    apply ByteArray.ext
    simp [Text.octets, List.map_map, Function.comp_def]
  rw [Text.fromOctets?, bytes]
  simp [String.fromUTF8?, key.val.isValidUTF8, Text.ofString?, bounded, key.property]

theorem ofFinset_members {Key : Type} [LinearOrder Key] (layout : OrderedSet Key) : ofFinset (members layout) = layout := by
  have sorted : layout.keys.Pairwise (· ≤ ·) := List.pairwise_map.mpr (layout.ordered.imp le_of_lt)
  have recovered : (members layout).sort = layout.keys := (List.toFinset_sort (· ≤ ·) layout.keys_nodup).mpr sorted
  apply OrderedMap.ext
  change (members layout).sort.map (·, ()) = layout.entries
  rw [recovered]
  simp [OrderedMap.keys, List.map_map, Function.comp_def]

end Silmaril.Proofs.Formats.Dasl.ShortKeySet
