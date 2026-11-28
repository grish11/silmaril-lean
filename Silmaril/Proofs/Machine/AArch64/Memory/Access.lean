module

public import Silmaril.Proofs.Machine.AArch64.Memory.Fetch

/-!
# AArch64 loads and stores: proofs

Proofs for the loads and stores of `Silmaril.Machine.AArch64.Memory.Thms`.

Method. `load` and `fetchWord` are `readLE` with read and with execute permission, and
`store` is `Memory.writeBytes` on the bytes of the value. So the statements about reads are
proved once, for `readLE` with any access kind, and every proof goes through the lemmas of
`Silmaril.Process.Memory`, with `bytesLE_length` and `bytesLE_getElem` to pass between byte
`i` of the list and bits `8i+7 : 8i` of the value.

* `readLE_eq_some_iff_bytes`: `Memory.readWith_permitted` and `Memory.readWith_get` in one
  direction, `Memory.readWith_eq` in the other. `load_eq_some_iff_bytes` is its case for
  read.
* `exists_readWith_of_stored`: a permitted span whose bytes all have a stored value is read
  by `Memory.readWith_eq`, with the list of those bytes.
* `readLE_eq_none_iff_bytes`: if the span is permitted and the read fails, some byte has no
  stored value, since otherwise `exists_readWith_of_stored` reads the span. Conversely a
  successful read is permitted (`Memory.readWith_permitted`) and has every byte
  (`Memory.readWith_get`).
* `readLE_eq_none_iff_of_wellFormed`: each byte of a permitted span lies in a region
  (`isSome_get?_of_permits`), so `Memory.WellFormed.backed` gives it a stored value, and
  `exists_readWith_of_stored` reads the span (`exists_readWith_of_wellFormed`).
* `load_zero`: no byte is read, and the start address of a 64-bit vector is below `2^64`.
* `store_eq_some_iff`: the definition of `Memory.writeBytes`, by cases on the permission.
* `store_get?`: `Memory.install_get` for a byte the store wrote, `Memory.install_outside`
  for any other.
* `load_store_same`: `Memory.install_get` gives back each byte that was written.
* `readLE_store_of_disjoint`: a store changes only its own bytes
  (`Memory.writeBytes_writesOnly`), so a read of other bytes is unchanged
  (`Memory.WritesWithin.readWith`), for every access kind. `load_store_of_disjoint` and
  `fetchWord_store_of_disjoint` are its cases for read and for execute.
* `not_permitted_of_span_past_limit`: `Memory.checkSpan_iff` asks for
  `address + n ≤ 2^64`. `readLE_eq_none_of_span_past_limit` and
  `store_eq_none_of_span_past_limit` follow.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.AArch64.Memory

open Silmaril.Process (Memory Byte Access)
open Silmaril.Machine.AArch64

/-! ## Reads with any access kind -/

/-- A read gives `value` exactly when every byte may be accessed and byte `i` of the memory
holds bits `8i+7 : 8i` of `value`. -/
theorem readLE_eq_some_iff_bytes {memory : Memory} {access : Access} {address : BitVec 64}
    {n : Nat} {value : BitVec (8 * n)} :
    readLE memory access address n = some value ↔
      memory.Permitted access address.toNat n ∧
        ∀ i < n, memory.bytes.get? (address.toNat + i) = some (value.extractLsb' (8 * i) 8) := by
  rw [readLE_eq_some_iff]
  constructor
  · intro read
    refine ⟨Memory.readWith_permitted read, fun i hi => ?_⟩
    have inside : i < (bytesLE n value).length := by rw [bytesLE_length]; exact hi
    rw [Memory.readWith_get read i inside, bytesLE_getElem]
  · rintro ⟨permitted, stored⟩
    have read := Memory.readWith_eq memory access address.toNat (bytesLE n value)
      (by rw [bytesLE_length]; exact permitted)
      (fun i hi => by rw [bytesLE_getElem]; exact stored i (by rwa [bytesLE_length] at hi))
    rwa [bytesLE_length] at read

/-- In a well-formed memory, a byte that a region maps with some permission has a stored
value. -/
theorem isSome_get?_of_permits {memory : Memory} {pageSize : Nat}
    (wellFormed : memory.WellFormed pageSize) {access : Access} {location : Nat}
    (allowed : memory.permits access location = true) :
    (memory.bytes.get? location).isSome = true := by
  rw [Memory.permits, List.any_eq_true] at allowed
  obtain ⟨region, member, mapped⟩ := allowed
  rw [Bool.and_eq_true, decide_eq_true_eq] at mapped
  exact wellFormed.backed region member location mapped.1

/-- A checked read of a permitted span succeeds if every byte of the span has a stored
value. -/
theorem exists_readWith_of_stored {memory : Memory} {access : Access} {address n : Nat}
    (permitted : memory.Permitted access address n)
    (stored : ∀ i < n, (memory.bytes.get? (address + i)).isSome = true) :
    ∃ bytes, memory.readWith access address n = some bytes := by
  let bytes : List Byte := (List.range n).map fun i => (memory.bytes.get? (address + i)).getD 0
  have length : bytes.length = n := by simp [bytes]
  have found : ∀ i (h : i < bytes.length), memory.bytes.get? (address + i) = some bytes[i] := by
    intro i h
    obtain ⟨byte, present⟩ := Option.isSome_iff_exists.mp (stored i (by rwa [length] at h))
    simp only [bytes, List.getElem_map, List.getElem_range, present, Option.getD_some]
  have read := Memory.readWith_eq memory access address bytes (by rw [length]; exact permitted)
    found
  rw [length] at read
  exact ⟨bytes, read⟩

/-- In a well-formed memory, a checked read of a permitted span succeeds. -/
theorem exists_readWith_of_wellFormed {memory : Memory} {pageSize : Nat}
    (wellFormed : memory.WellFormed pageSize) {access : Access} {address n : Nat}
    (permitted : memory.Permitted access address n) :
    ∃ bytes, memory.readWith access address n = some bytes :=
  exists_readWith_of_stored permitted fun i hi => isSome_get?_of_permits wellFormed
    (((Memory.checkSpan_iff memory access address n).mp permitted).2.2 i hi)

/-- A read fails exactly when some byte may not be accessed or some byte of the span has no
stored value. -/
theorem readLE_eq_none_iff_bytes {memory : Memory} {access : Access} {address : BitVec 64}
    {n : Nat} :
    readLE memory access address n = none ↔
      ¬ memory.Permitted access address.toNat n ∨
        ∃ i < n, memory.bytes.get? (address.toNat + i) = none := by
  rw [readLE, Option.map_eq_none_iff]
  constructor
  · intro failed
    by_cases permitted : memory.Permitted access address.toNat n
    · refine Or.inr (Classical.byContradiction fun present => ?_)
      have stored : ∀ i < n, (memory.bytes.get? (address.toNat + i)).isSome = true := by
        intro i hi
        rw [Option.isSome_iff_ne_none]
        exact fun absent => present ⟨i, hi, absent⟩
      obtain ⟨bytes, read⟩ := exists_readWith_of_stored permitted stored
      rw [read] at failed
      cases failed
    · exact Or.inl permitted
  · intro cause
    cases read : memory.readWith access address.toNat n with
    | none => rfl
    | some bytes =>
      rcases cause with refused | ⟨i, hi, absent⟩
      · exact absurd (Memory.readWith_permitted read) refused
      · have found := Memory.readWith_get read i (by rw [Memory.readWith_length read]; exact hi)
        rw [absent] at found
        cases found

/-- In a well-formed memory, a read fails exactly when some byte may not be accessed. -/
theorem readLE_eq_none_iff_of_wellFormed {memory : Memory} {pageSize : Nat}
    (wellFormed : memory.WellFormed pageSize) {access : Access} {address : BitVec 64}
    {n : Nat} :
    readLE memory access address n = none ↔ ¬ memory.Permitted access address.toNat n := by
  rw [readLE, Option.map_eq_none_iff]
  constructor
  · intro failed permitted
    obtain ⟨bytes, read⟩ := exists_readWith_of_wellFormed wellFormed permitted
    rw [read] at failed
    cases failed
  · intro refused
    cases read : memory.readWith access address.toNat n with
    | none => rfl
    | some bytes => exact absurd (Memory.readWith_permitted read) refused

/-- A span that passes `2^64` is not permitted, whatever the regions are. -/
theorem not_permitted_of_span_past_limit (memory : Memory) (access : Access) (address n : Nat)
    (past : 2 ^ 64 < address + n) : ¬ memory.Permitted access address n := by
  intro permitted
  have below : address + n ≤ 2 ^ 64 :=
    ((Memory.checkSpan_iff memory access address n).mp permitted).2.1
  omega

/-- A read whose span passes `2^64` fails. -/
theorem readLE_eq_none_of_span_past_limit (memory : Memory) (access : Access)
    (address : BitVec 64) (n : Nat) (past : 2 ^ 64 < address.toNat + n) :
    readLE memory access address n = none := by
  rw [readLE, Option.map_eq_none_iff]
  cases read : memory.readWith access address.toNat n with
  | none => rfl
  | some bytes =>
    exact absurd (Memory.readWith_permitted read)
      (not_permitted_of_span_past_limit memory access address.toNat n past)

/-! ## Loads -/

/-- A load gives `value` exactly when every byte may be read and byte `i` of the memory
holds bits `8i+7 : 8i` of `value`. -/
theorem load_eq_some_iff_bytes {memory : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    load memory address n = some value ↔
      memory.Permitted .read address.toNat n ∧
        ∀ i < n, memory.bytes.get? (address.toNat + i) = some (value.extractLsb' (8 * i) 8) :=
  readLE_eq_some_iff_bytes

/-- A load of no byte gives the empty value, at every address. -/
theorem load_zero (memory : Memory) (address : BitVec 64) : load memory address 0 = some 0#0 := by
  refine load_eq_some_iff_bytes.mpr ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  exact (Memory.checkSpan_iff memory .read address.toNat 0).mpr
    ⟨address.isLt, Nat.le_of_lt address.isLt, fun offset h => absurd h (Nat.not_lt_zero offset)⟩

/-- A one-byte load gives `byte` exactly when the byte may be read and the memory holds
`byte` there. -/
theorem loadByte_eq_some_iff_bytes {memory : Memory} {address : BitVec 64} {byte : BitVec 8} :
    loadByte memory address = some byte ↔
      memory.Permitted .read address.toNat 1 ∧ memory.bytes.get? address.toNat = some byte := by
  refine (load_eq_some_iff_bytes (n := 1) (value := byte)).trans (and_congr_right fun _ => ?_)
  constructor
  · intro stored
    simpa using stored 0 (by omega)
  · intro stored i hi
    obtain rfl : i = 0 := by omega
    simpa using stored

/-! ## Stores -/

/-- A store succeeds exactly when every byte may be written, and then the memory after it
is the memory before with the bytes of `value` installed at `address`. -/
theorem store_eq_some_iff {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    store memory address n value = some after ↔
      memory.Permitted .write address.toNat n ∧
        after =
          { memory with bytes := Memory.install memory.bytes address.toNat (bytesLE n value) } := by
  rw [store, Memory.writeBytes, bytesLE_length]
  by_cases permitted : memory.Permitted .write address.toNat n
  · have check : memory.checkSpan .write address.toNat n = true := permitted
    simp only [check, ↓reduceIte, Option.some.injEq, permitted, true_and]
    exact eq_comm
  · have check : ¬ memory.checkSpan .write address.toNat n = true := permitted
    simp [check, permitted]

/-- A store fails exactly when some byte may not be written. -/
theorem store_eq_none_iff {memory : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    store memory address n value = none ↔ ¬ memory.Permitted .write address.toNat n := by
  rw [Option.eq_none_iff_forall_ne_some]
  constructor
  · intro failed permitted
    exact failed _ (store_eq_some_iff.mpr ⟨permitted, rfl⟩)
  · intro refused after stored
    exact refused (store_eq_some_iff.mp stored).1

/-- A store of no byte gives the memory back, at every address. -/
theorem store_zero (memory : Memory) (address : BitVec 64) (value : BitVec (8 * 0)) :
    store memory address 0 value = some memory := by
  refine store_eq_some_iff.mpr ⟨?_, rfl⟩
  exact (Memory.checkSpan_iff memory .write address.toNat 0).mpr
    ⟨address.isLt, Nat.le_of_lt address.isLt, fun offset h => absurd h (Nat.not_lt_zero offset)⟩

/-- The byte table after a store: the byte at `address + i`, for `i < n`, is bits
`8i+7 : 8i` of the value, and every other byte is the one from before. -/
theorem store_get? {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after)
    (location : Nat) :
    after.bytes.get? location =
      if address.toNat ≤ location ∧ location < address.toNat + n then
        some (value.extractLsb' (8 * (location - address.toNat)) 8)
      else memory.bytes.get? location := by
  obtain ⟨-, rfl⟩ := store_eq_some_iff.mp stored
  by_cases written : address.toNat ≤ location ∧ location < address.toNat + n
  · have inside : location - address.toNat < (bytesLE n value).length := by
      rw [bytesLE_length]; omega
    have found := Memory.install_get memory.bytes address.toNat (bytesLE n value)
      (location - address.toNat) inside
    rw [show address.toNat + (location - address.toNat) = location by omega,
      bytesLE_getElem] at found
    rw [ite_eq_left written]
    exact found
  · rw [ite_eq_right written]
    exact Memory.install_outside memory.bytes address.toNat (bytesLE n value) location
      (by rw [bytesLE_length]; omega)

/-- A store whose span passes `2^64` fails. -/
theorem store_eq_none_of_span_past_limit (memory : Memory) (address : BitVec 64) (n : Nat)
    (value : BitVec (8 * n)) (past : 2 ^ 64 < address.toNat + n) :
    store memory address n value = none :=
  store_eq_none_iff.mpr (not_permitted_of_span_past_limit memory .write address.toNat n past)

/-- A load after a store at the same address and size gives the stored value, if the bytes
may be read. -/
theorem load_store_same {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after)
    (readable : memory.Permitted .read address.toNat n) : load after address n = some value := by
  obtain ⟨-, rfl⟩ := store_eq_some_iff.mp stored
  refine load_eq_some_iff_bytes.mpr ⟨readable, fun i hi => ?_⟩
  have inside : i < (bytesLE n value).length := by rw [bytesLE_length]; exact hi
  rw [← bytesLE_getElem n value i inside]
  exact Memory.install_get _ _ _ _ inside

/-- A store leaves every checked read of bytes it did not write unchanged, whatever the
access kind of the read. -/
theorem readLE_store_of_disjoint {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after)
    (access : Access) (other : BitVec 64) (k : Nat)
    (disjoint : other.toNat + k ≤ address.toNat ∨ address.toNat + n ≤ other.toNat) :
    readLE after access other k = readLE memory access other k := by
  have frame := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp
    (Memory.writeBytes_writesOnly stored)
  rw [bytesLE_length] at frame
  have outside : ∀ offset < k,
      ¬ (address.toNat ≤ other.toNat + offset ∧ other.toNat + offset < address.toNat + n) := by
    omega
  rw [readLE, readLE, frame.readWith outside]

end Silmaril.Proofs.Machine.AArch64.Memory
