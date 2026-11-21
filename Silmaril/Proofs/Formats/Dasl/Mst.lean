module

public import Silmaril.Formats.Dasl.Mst.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.Mst

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Mst

variable {Name : Type}

theorem prefixLength_le (previous key : Key) : prefixLength previous key ≤ previous.length := by
  induction previous generalizing key with
  | nil => exact Nat.le_refl _
  | cons first previous ih =>
    cases key with
    | nil => exact Nat.zero_le _
    | cons next key =>
      by_cases same : first = next
      · simpa [prefixLength, same] using ih key
      · simp [prefixLength, same]

theorem take_prefix (previous key : Key) : previous.take (prefixLength previous key) = key.take (prefixLength previous key) := by
  induction previous generalizing key with
  | nil => rfl
  | cons first previous ih =>
    cases key with
    | nil => rfl
    | cons next key =>
      by_cases same : first = next
      · simp [prefixLength, same, ih]
      · simp [prefixLength, same]

theorem common_prefix_le (left right : Key) (count : Nat) (leftBound : count ≤ left.length)
    (rightBound : count ≤ right.length) (same : left.take count = right.take count) : count ≤ prefixLength left right := by
  induction count generalizing left right with
  | zero => exact Nat.zero_le _
  | succ count ih =>
    cases left with
    | nil => simp at leftBound
    | cons first left =>
      cases right with
      | nil => simp at rightBound
      | cons next right =>
        obtain ⟨rfl, rest⟩ := List.cons.inj same
        simpa [prefixLength] using Nat.succ_le_succ
          (ih left right (Nat.le_of_succ_le_succ leftBound) (Nat.le_of_succ_le_succ rightBound) rest)

theorem expand_compress (previous : Key) (entries : List (Entry Name)) :
    expandEntries? previous (compressEntries previous entries) = some entries := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry remaining ih =>
    have same : previous.take (prefixLength previous entry.key) ++ entry.key.drop (prefixLength previous entry.key) = entry.key :=
      (congrArg (· ++ _) (take_prefix previous entry.key)).trans (List.take_append_drop ..)
    simp [compressEntries, expandEntries?, same, ih]

theorem compress_expand (previous : Key) (entries : List (WireEntry Name)) {expanded : List (Entry Name)}
    (hit : expandEntries? previous entries = some expanded) : compressEntries previous expanded = entries := by
  induction entries generalizing previous expanded with
  | nil => cases hit; rfl
  | cons entry remaining ih =>
    let key := previous.take entry.shared ++ entry.suffix
    change (if prefixLength previous key = entry.shared then
      (expandEntries? key remaining).bind (fun tail => some (⟨key, entry.record, entry.right⟩ :: tail))
      else none) = some expanded at hit
    by_cases canonical : prefixLength previous key = entry.shared
    · have bound : entry.shared ≤ previous.length := canonical ▸ prefixLength_le previous key
      have suffix : key.drop entry.shared = entry.suffix := calc
        key.drop entry.shared = key.drop (previous.take entry.shared).length :=
          congrArg key.drop (List.length_take_of_le bound).symm
        _ = entry.suffix := List.drop_append_length
      cases found : expandEntries? key remaining with
      | none => simp [canonical, found] at hit
      | some tail =>
        have same : (⟨key, entry.record, entry.right⟩ : Entry Name) :: tail = expanded := by
          simpa [canonical, found] using hit
        subst expanded
        rcases entry with ⟨shared, suffixValue, record, right⟩
        simp only [compressEntries, canonical, suffix, ih key found]
    · simp [canonical] at hit

private theorem wireEntry_roundtrip {entry : WireEntry Name} {value : Shallow Name}
    (hit : encodeWireEntry? entry = some value) : decodeWireEntry? value = some entry := by
  by_cases inRange : entry.shared < 2^63
  · simp only [encodeWireEntry?, ite_eq_left inRange, Option.some.injEq] at hit
    subst value
    have same : (UInt64.ofNat entry.shared).toNat = entry.shared := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
      exact inRange.trans (by decide)
    cases entry with
    | mk shared suffix record right =>
      cases right <;> (simp [decodeWireEntry?, encodeChild, decodeChild, decodeRecord, same]; exact inRange)
  · simp only [encodeWireEntry?, ite_eq_right inRange, reduceCtorEq] at hit

theorem wire_roundtrip {node : WireNode Name} {value : Shallow Name}
    (hit : encodeWireNode? node = some value) : decodeWireNode? value = some node := by
  obtain ⟨entries, encoded, shape⟩ := Option.bind_eq_some_iff.mp hit
  change some _ = some value at shape
  have same := Option.some.inj shape
  subst value
  let codec : Encode.PartialCodec (WireEntry Name) (Shallow Name) :=
    ⟨encodeWireEntry?, decodeWireEntry?, fun _ _ => wireEntry_roundtrip⟩
  have read : entries.mapM decodeWireEntry? = some node.entries := codec.list_roundtrip encoded
  cases node with
  | mk left original =>
    cases left <;> simp [decodeWireNode?, encodeChild, decodeChild, Encode.list.recovers, read]

end Silmaril.Proofs.Formats.Dasl.Mst
