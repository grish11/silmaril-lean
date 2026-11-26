module

public import Silmaril.Languages.Starlark.Lists.GoDictionary.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Agreement
import Silmaril.Proofs.Languages.Starlark.Lists.GoDictionary.Slots

public section

namespace Silmaril.Languages.Starlark.Lists.GoDictionary

/-- Exact modulo-2^32 integer hash, with distinct signed and magnitude cases. -/
theorem intHash_toNat (value : Int) :
    (intHash value).toNat =
      (12582917 * ((if -(2 ^ 31) ≤ value ∧ value < 2 ^ 31
        then (value % 2 ^ 32).toNat else value.natAbs) + 3)) % 2 ^ 32 :=
  Proofs.Languages.Starlark.Lists.GoDictionary.intHash_toNat value

theorem hashesAt_iff (heap : Heap) (depth : Nat) (key : Value) (out : UInt32) :
    HashesAt heap depth key out ↔ hashAt heap depth key = .ok out :=
  Proofs.Languages.Starlark.Lists.GoDictionary.hashesAt_iff heap depth key out

theorem looksUp_iff (heap : Heap) (bucket : Bucket) (key : Value)
    (out : Except Error (UInt32 × Option (Row × Nat))) :
    LooksUp heap bucket key out ↔ lookupWithHash heap bucket key = out :=
  Proofs.Languages.Starlark.Lists.GoDictionary.looksUp_iff heap bucket key out

theorem slot_count (bucket : Bucket) : bucket.slots.length = 8 :=
  Proofs.Languages.Starlark.Lists.GoDictionary.slot_count bucket

/-- A new key fills the highest vacant slot. -/
theorem insert_slots (bucket : Bucket) (row : Row) (room : bucket.rows.length < 8) :
    (bucket.insert row room).slots = bucket.slots.set (7 - bucket.rows.length) (some row) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.insert_slots bucket row room

theorem insert_keys (bucket : Bucket) (row : Row) (room : bucket.rows.length < 8) :
    (bucket.insert row room).keys = bucket.keys ++ [row.key] := by
  simp [Bucket.insert, Bucket.keys]

/-- The candidate selected by lookup names a live row. -/
theorem lookup_hit_row (heap : Heap) (bucket : Bucket) (key : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap bucket key = .ok (hash, some hit)) :
    bucket.rows[hit.2]? = some hit.1 :=
  Proofs.Languages.Starlark.Lists.GoDictionary.lookup_hit_row heap bucket key hash hit found

/-- Replacement updates exactly the physical slot named by the probe. -/
theorem replace_slots (bucket : Bucket) (hit : Row × Nat) (value : Value) :
    (bucket.replace hit value).slots =
      bucket.slots.set (8 - bucket.rows.length + hit.2) (some { hit.1 with value }) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.replace_slots bucket hit value

theorem set_hit_slots (heap : Heap) (bucket : Bucket) (key value : Value) (hash : UInt32)
    (hit : Row × Nat) (found : lookupWithHash heap bucket key = .ok (hash, some hit)) :
    (set heap bucket key value).map Bucket.slots = .ok
      (bucket.slots.set (8 - bucket.rows.length + hit.2) (some { hit.1 with value })) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.set_hit_slots heap bucket key value hash hit found

theorem set_miss_slots (heap : Heap) (bucket : Bucket) (key value : Value) (hash : UInt32)
    (missing : lookupWithHash heap bucket key = .ok (hash, none)) (room : bucket.rows.length < 8) :
    (set heap bucket key value).map Bucket.slots = .ok
      (bucket.slots.set (7 - bucket.rows.length) (some ⟨hash, key, value⟩)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.set_miss_slots heap bucket key value hash missing room

/-- Replacing the selected row preserves its stored hash and original key, and
the order of keys in both slot traversal and insertion order. -/
theorem replace_keeps_keys (bucket : Bucket) (hit : Row × Nat) (value : Value)
    (present : bucket.rows[hit.2]? = some hit.1) :
    (bucket.replace hit value).rows.map (fun row => (row.hash, row.key)) =
      bucket.rows.map (fun row => (row.hash, row.key)) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.replace_keeps_keys bucket hit value present

/-- Probing visits precisely the matching occupied slots in ascending order,
including collisions between unequal keys. -/
theorem candidates_slots (bucket : Bucket) (hash : UInt32) :
    (bucket.candidates hash).map Prod.fst =
      bucket.slots.filterMap (fun cell => cell.filter fun row => row.hash == hash) :=
  Proofs.Languages.Starlark.Lists.GoDictionary.candidates_slots bucket hash

end Silmaril.Languages.Starlark.Lists.GoDictionary
