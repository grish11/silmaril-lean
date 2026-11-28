module

public import Silmaril.Machine.AArch64.Memory.Defs
import Silmaril.Proofs.Machine.AArch64.Memory.Fetch
import Silmaril.Proofs.Machine.AArch64.Memory.Access

/-!
# AArch64 memory: little-endian bytes, instruction fetch, loads and stores

Statements about `Silmaril.Machine.AArch64.Memory.Defs`.

* **Bytes of a value.** `bytesLE_length`: `bytesLE n v` has `n` bytes. `bytesLE_getElem`:
  byte `i` is bits `8i+7 : 8i` of `v`. (Arm's `Mem`: byte `i`, at `address + i`, is
  `value[i*:8]`.)
* **Value of bytes.** `valueLE_lt`: `k` bytes denote a number below `2 ^ (8 * k)`.
  `toNat_ofBytesLE`: the value of exactly `n` bytes is the number the bytes denote.
  `valueLE_bytesLE`: the bytes of a value denote the number of the value.
  `ofBytesLE_four_toNat`, `ofBytesLE_four_append`: a four-byte word as a sum and as a
  concatenation; the first byte is the least significant.
* **Round trips.** `ofBytesLE_bytesLE`: the bytes of a value give the value back.
  `bytesLE_ofBytesLE`: the value of exactly `n` bytes gives the bytes back.
* **Checked reads.** `readLE_eq_some_iff`: `readLE` gives `value` exactly when the reused
  memory's `readWith` gives the bytes of `value`. `readLE_eq_none_iff`: it fails exactly
  when `readWith` fails. `readLE_eq_some_iff_bytes`: it gives `value` exactly when every
  byte may be accessed and the byte at `address + i` is bits `8i+7 : 8i` of `value`.
  `readLE_eq_none_iff_bytes`: it fails exactly when some byte may not be accessed or some
  byte of the span has no stored value. `readLE_eq_none_iff_of_wellFormed`: in a
  well-formed memory it fails exactly when some byte may not be accessed.
  `readLE_eq_none_of_span_past_limit`: it fails if the span passes `2^64`.
* **Instruction fetch.** `fetchWord_eq_some_iff`, `fetchWord_eq_none_iff`: the first two
  facts for `fetchWord` and `fetchBytes` on four bytes, so a fetch needs execute
  permission and no other. `fetchWord_eq_some_iff_bytes`, `fetchWord_eq_none_iff_bytes`,
  `fetchWord_eq_none_iff_of_wellFormed`, `fetchWord_eq_none_of_span_past_limit`: the other
  four, for four bytes and execute permission.
* **Installed code.** `wordsBytes_nil`, `wordsBytes_cons`: the bytes of a list of words
  are the four bytes of each word, in order. `wordsBytes_length`: four bytes for each
  word, and no more. `fetchWord_installWords`: after instruction words are installed at
  `base`, a fetch at `base + 4 * i` gives word `i`.
* **Loads.** `load_eq_some_iff`, `load_eq_none_iff`: a load gives `value` exactly when the
  reused memory's `readBytes` gives the bytes of `value`, and fails exactly when
  `readBytes` fails. `load_eq_some_iff_bytes`: a load gives `value` exactly when every byte
  may be read and the byte at `address + i` is bits `8i+7 : 8i` of `value`.
  `load_eq_none_iff_bytes`: a load fails exactly when some byte may not be read or some
  byte of the span has no stored value. `load_eq_none_iff_of_wellFormed`: in a well-formed
  memory, that is exactly when some byte may not be read. `load_zero`: a load of no byte
  gives the empty value. `load_eq_none_of_span_past_limit`: a load fails if the span passes
  `2^64`.
* **One-byte loads.** `loadByte_eq_load`: `loadByte` is `load` of one byte.
  `loadByte_eq_some_iff_bytes`: it gives `byte` exactly when the byte may be read and the
  memory holds `byte` there. `loadByte_eq_none_iff`: it fails exactly when `readBytes` of
  that byte fails.
* **Stores.** `store_eq_some_iff`: a store succeeds exactly when every byte may be
  written, and the memory after it has the bytes of the value installed.
  `store_eq_none_iff`: a store fails exactly when some byte may not be written.
  `store_get?`: the byte table after a store, address by address: bits `8i+7 : 8i` of the
  value at `address + i`, the old byte everywhere else. `store_zero`: a store of no byte
  gives the memory back. `store_eq_none_of_span_past_limit`: a store fails if the span
  passes `2^64`. `store_regions`, `store_wellFormed`: a store keeps the regions and
  well-formedness.
* **After a store.** `load_store_same`: a load at the address and size of the store gives
  the stored value, if the bytes may be read. `load_store_of_disjoint`,
  `fetchWord_store_of_disjoint`: a load or a fetch of bytes the store did not write gives
  what it gave before.

Here "may be read", "may be written" and "may be accessed" are `Memory.Permitted` of the
reused memory: the span stays below `2^64` and each of its bytes lies in a region with the
permission.

**Names.** For `readLE`, `fetchWord` and `load`, a plain name (`…_eq_some_iff`,
`…_eq_none_iff`) is the form through the read of the reused memory (`readWith`,
`fetchBytes`, `readBytes`). The suffix `_bytes` is the form with `Memory.Permitted` and the
byte table.

**The top of the address space.** The four `…_of_span_past_limit` statements say that an
access whose bytes would continue past `2^64` fails. This is a behaviour Arm permits: the
Arm ARM leaves the address of the bytes above the boundary UNKNOWN and allows it to be one
that always faults. See "A span passing `2^64` is refused" in the module documentation of
`Silmaril.Machine.AArch64.Memory.Defs`, which has the citations. For an access of 1, 2, 4
or 8 bytes at an address that is a multiple of its size, the hypothesis
`2 ^ 64 < address.toNat + n` cannot hold. So for a fetch these statements concern only an
address that is not a multiple of 4, where Arm does not fetch at all.

Proofs longer than a few lines: modules `Silmaril.Proofs.Machine.AArch64.Memory.Fetch`
(bytes and fetch) and `Silmaril.Proofs.Machine.AArch64.Memory.Access` (loads and stores).
`bytesLE_length` and `bytesLE_getElem` are one line each and are proved there too, because
the longer proofs use them.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64

open Silmaril.Process (Memory Byte Access)

/-! ## Little-endian bytes -/

/-- `bytesLE n` gives `n` bytes. -/
theorem bytesLE_length (n : Nat) (v : BitVec (8 * n)) : (bytesLE n v).length = n :=
  Silmaril.Proofs.Machine.AArch64.Memory.bytesLE_length n v

/-- Byte `i` is bits `8i+7 : 8i` of the value. -/
theorem bytesLE_getElem (n : Nat) (v : BitVec (8 * n)) (i : Nat) (h : i < (bytesLE n v).length) :
    (bytesLE n v)[i] = v.extractLsb' (8 * i) 8 :=
  Silmaril.Proofs.Machine.AArch64.Memory.bytesLE_getElem n v i h

/-- `k` bytes denote a number below `2 ^ (8 * k)`. -/
theorem valueLE_lt (bytes : List Byte) : valueLE bytes < 2 ^ (8 * bytes.length) :=
  Silmaril.Proofs.Machine.AArch64.Memory.valueLE_lt bytes

/-- **Round trip from a value.** Writing a value as `n` bytes and reading the bytes back
gives the value. -/
theorem ofBytesLE_bytesLE (n : Nat) (v : BitVec (8 * n)) : ofBytesLE n (bytesLE n v) = v :=
  Silmaril.Proofs.Machine.AArch64.Memory.ofBytesLE_bytesLE n v

/-- **Round trip from bytes.** Reading exactly `n` bytes as a value and writing the value
as bytes gives the bytes. With `bytesLE_getElem`: bits `8i+7 : 8i` of `ofBytesLE n bytes`
are `bytes[i]`. -/
theorem bytesLE_ofBytesLE {n : Nat} (bytes : List Byte) (h : bytes.length = n) :
    bytesLE n (ofBytesLE n bytes) = bytes :=
  Silmaril.Proofs.Machine.AArch64.Memory.bytesLE_ofBytesLE bytes h

/-- **The number of a value.** The value of exactly `n` bytes is the number the bytes
denote: byte `i` counts `256 ^ i` times. With more than `n` bytes the value would be cut. -/
theorem toNat_ofBytesLE {n : Nat} (bytes : List Byte) (h : bytes.length = n) :
    (ofBytesLE n bytes).toNat = valueLE bytes :=
  Silmaril.Proofs.Machine.AArch64.Memory.toNat_ofBytesLE bytes h

/-- **The number of the bytes.** The `n` bytes of a value denote the number of the value. -/
theorem valueLE_bytesLE (n : Nat) (v : BitVec (8 * n)) : valueLE (bytesLE n v) = v.toNat :=
  Silmaril.Proofs.Machine.AArch64.Memory.valueLE_bytesLE n v

/-- The number a four-byte word denotes: the first byte is the least significant. -/
theorem ofBytesLE_four_toNat (b0 b1 b2 b3 : Byte) :
    (ofBytesLE 4 [b0, b1, b2, b3]).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat :=
  Silmaril.Proofs.Machine.AArch64.Memory.ofBytesLE_four_toNat b0 b1 b2 b3

/-- A four-byte word as a concatenation: the last byte is the most significant. -/
theorem ofBytesLE_four_append (b0 b1 b2 b3 : Byte) :
    (ofBytesLE 4 [b0, b1, b2, b3] : BitVec 32) = b3 ++ b2 ++ b1 ++ b0 :=
  Silmaril.Proofs.Machine.AArch64.Memory.ofBytesLE_four_append b0 b1 b2 b3

/-! ## Checked little-endian reads -/

/-- A read gives `value` exactly when the checked byte read of the reused memory gives the
bytes of `value`, least significant first. -/
theorem readLE_eq_some_iff {memory : Memory} {access : Access} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    readLE memory access address n = some value ↔
      memory.readWith access address.toNat n = some (bytesLE n value) :=
  Silmaril.Proofs.Machine.AArch64.Memory.readLE_eq_some_iff

/-- A read fails exactly when the checked byte read of the reused memory fails.
`readLE_eq_none_iff_bytes` says when that is: the span passes `2^64`, a byte lacks the
permission, or a byte has no stored value. -/
theorem readLE_eq_none_iff {memory : Memory} {access : Access} {address : BitVec 64} {n : Nat} :
    readLE memory access address n = none ↔ memory.readWith access address.toNat n = none := by
  rw [readLE, Option.map_eq_none_iff]

/-- **When a read succeeds.** A read gives `value` exactly when the `n` bytes may be
accessed and, for each `i < n`, the byte stored at `address + i` is bits `8i+7 : 8i` of
`value`. -/
theorem readLE_eq_some_iff_bytes {memory : Memory} {access : Access} {address : BitVec 64}
    {n : Nat} {value : BitVec (8 * n)} :
    readLE memory access address n = some value ↔
      memory.Permitted access address.toNat n ∧
        ∀ i < n, memory.bytes.get? (address.toNat + i) = some (value.extractLsb' (8 * i) 8) :=
  Silmaril.Proofs.Machine.AArch64.Memory.readLE_eq_some_iff_bytes

/-- **When a read fails.** A read fails exactly when the `n` bytes may not be accessed (the
span passes `2^64`, or a byte lacks the permission), or some byte of the span has no
stored value. This needs no well-formedness. -/
theorem readLE_eq_none_iff_bytes {memory : Memory} {access : Access} {address : BitVec 64}
    {n : Nat} :
    readLE memory access address n = none ↔
      ¬ memory.Permitted access address.toNat n ∨
        ∃ i < n, memory.bytes.get? (address.toNat + i) = none :=
  Silmaril.Proofs.Machine.AArch64.Memory.readLE_eq_none_iff_bytes

/-- **When a read fails, in a well-formed memory.** There every mapped byte has a stored
value, so a read fails exactly when the `n` bytes may not be accessed: the span passes
`2^64` or a byte lacks the permission. -/
theorem readLE_eq_none_iff_of_wellFormed {memory : Memory} {pageSize : Nat}
    (wellFormed : memory.WellFormed pageSize) {access : Access} {address : BitVec 64}
    {n : Nat} :
    readLE memory access address n = none ↔ ¬ memory.Permitted access address.toNat n :=
  Silmaril.Proofs.Machine.AArch64.Memory.readLE_eq_none_iff_of_wellFormed wellFormed

/-- **The top of the address space.** A read whose `n` bytes would continue past `2^64`
fails, whatever the regions and the stored bytes are. Arm permits this: it leaves the
address of the bytes above the boundary UNKNOWN and allows it to be one that always faults
(module documentation of `Silmaril.Machine.AArch64.Memory.Defs`). A span that ends exactly
at `2^64` is not refused by this. For 1, 2, 4 or 8 bytes at a multiple of that size the
hypothesis cannot hold, so the statement concerns unaligned accesses. -/
theorem readLE_eq_none_of_span_past_limit (memory : Memory) (access : Access)
    (address : BitVec 64) (n : Nat) (past : 2 ^ 64 < address.toNat + n) :
    readLE memory access address n = none :=
  Silmaril.Proofs.Machine.AArch64.Memory.readLE_eq_none_of_span_past_limit memory access
    address n past

/-! ## Instruction fetch -/

/-- A fetch gives `word` exactly when the four bytes at `address`, read with execute
permission, are the bytes of `word`, least significant first. -/
theorem fetchWord_eq_some_iff {memory : Memory} {address : BitVec 64} {word : BitVec 32} :
    fetchWord memory address = some word ↔
      memory.fetchBytes address.toNat 4 = some (bytesLE 4 word) :=
  readLE_eq_some_iff (n := 4)

/-- A fetch fails exactly when the four-byte read with execute permission fails.
`fetchWord_eq_none_iff_bytes` says when that is. -/
theorem fetchWord_eq_none_iff {memory : Memory} {address : BitVec 64} :
    fetchWord memory address = none ↔ memory.fetchBytes address.toNat 4 = none :=
  readLE_eq_none_iff (n := 4)

/-- A fetch gives `word` exactly when the four bytes may be executed and, for each `i < 4`,
the byte stored at `address + i` is bits `8i+7 : 8i` of `word`. -/
theorem fetchWord_eq_some_iff_bytes {memory : Memory} {address : BitVec 64}
    {word : BitVec 32} :
    fetchWord memory address = some word ↔
      memory.Permitted .execute address.toNat 4 ∧
        ∀ i < 4, memory.bytes.get? (address.toNat + i) = some (word.extractLsb' (8 * i) 8) :=
  readLE_eq_some_iff_bytes (n := 4)

/-- A fetch fails exactly when the four bytes may not be executed (the span passes `2^64`,
or a byte lacks execute permission), or one of the four bytes has no stored value. -/
theorem fetchWord_eq_none_iff_bytes {memory : Memory} {address : BitVec 64} :
    fetchWord memory address = none ↔
      ¬ memory.Permitted .execute address.toNat 4 ∨
        ∃ i < 4, memory.bytes.get? (address.toNat + i) = none :=
  readLE_eq_none_iff_bytes (n := 4)

/-- In a well-formed memory, a fetch fails exactly when the four bytes may not be executed:
the span passes `2^64` or a byte lacks execute permission. -/
theorem fetchWord_eq_none_iff_of_wellFormed {memory : Memory} {pageSize : Nat}
    (wellFormed : memory.WellFormed pageSize) {address : BitVec 64} :
    fetchWord memory address = none ↔ ¬ memory.Permitted .execute address.toNat 4 :=
  readLE_eq_none_iff_of_wellFormed wellFormed (n := 4)

/-- A fetch whose four bytes would continue past `2^64` fails. The hypothesis cannot hold
at an address that is a multiple of 4: there `address.toNat + 4 ≤ 2 ^ 64`. So this concerns
only an address at which Arm does not fetch, because the PC alignment check comes first. -/
theorem fetchWord_eq_none_of_span_past_limit (memory : Memory) (address : BitVec 64)
    (past : 2 ^ 64 < address.toNat + 4) : fetchWord memory address = none :=
  readLE_eq_none_of_span_past_limit memory .execute address 4 past

/-! ## Installed code -/

/-- No words give no bytes. -/
theorem wordsBytes_nil : wordsBytes [] = [] :=
  rfl

/-- The bytes of a list of words are the four bytes of the first word, least significant
first, followed by the bytes of the other words. -/
theorem wordsBytes_cons (word : BitVec 32) (words : List (BitVec 32)) :
    wordsBytes (word :: words) = bytesLE 4 word ++ wordsBytes words :=
  Silmaril.Proofs.Machine.AArch64.Memory.wordsBytes_cons word words

/-- Each word gives four bytes, and there are no other bytes. -/
theorem wordsBytes_length (words : List (BitVec 32)) :
    (wordsBytes words).length = 4 * words.length :=
  Silmaril.Proofs.Machine.AArch64.Memory.wordsBytes_length words

/-- **Fetching installed code.** After the bytes of `words` are installed at `base`, a
fetch at `base + 4 * i` gives word `i`, provided its four bytes are executable. The
permission check already keeps these four bytes below `2^64`, so `base + 4 * i` does not
wrap. -/
theorem fetchWord_installWords (memory : Memory) (base : BitVec 64) (words : List (BitVec 32))
    (i : Nat) (hi : i < words.length)
    (permitted : memory.Permitted .execute (base.toNat + 4 * i) 4) :
    fetchWord { memory with bytes := Memory.install memory.bytes base.toNat (wordsBytes words) }
      (base + BitVec.ofNat 64 (4 * i)) = some words[i] :=
  Silmaril.Proofs.Machine.AArch64.Memory.fetchWord_installWords memory base words i hi permitted

/-! ## Loads and stores -/

/-- A load gives `value` exactly when the checked read of the reused memory gives the bytes
of `value`, least significant first. -/
theorem load_eq_some_iff {memory : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    load memory address n = some value ↔
      memory.readBytes address.toNat n = some (bytesLE n value) :=
  readLE_eq_some_iff

/-- A load fails exactly when the checked read of the reused memory fails.
`load_eq_none_iff_bytes` says when that is: the span passes `2^64`, a byte lacks read
permission, or a byte has no stored value. -/
theorem load_eq_none_iff {memory : Memory} {address : BitVec 64} {n : Nat} :
    load memory address n = none ↔ memory.readBytes address.toNat n = none :=
  readLE_eq_none_iff

/-- **When a load succeeds.** A load gives `value` exactly when the `n` bytes may be read
and, for each `i < n`, the byte stored at `address + i` is bits `8i+7 : 8i` of `value`. -/
theorem load_eq_some_iff_bytes {memory : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    load memory address n = some value ↔
      memory.Permitted .read address.toNat n ∧
        ∀ i < n, memory.bytes.get? (address.toNat + i) = some (value.extractLsb' (8 * i) 8) :=
  readLE_eq_some_iff_bytes

/-- **When a load fails.** A load fails exactly when the `n` bytes may not be read (the span
passes `2^64`, or a byte lacks read permission), or some byte of the span has no stored
value. This needs no well-formedness. -/
theorem load_eq_none_iff_bytes {memory : Memory} {address : BitVec 64} {n : Nat} :
    load memory address n = none ↔
      ¬ memory.Permitted .read address.toNat n ∨
        ∃ i < n, memory.bytes.get? (address.toNat + i) = none :=
  readLE_eq_none_iff_bytes

/-- **When a load fails, in a well-formed memory.** There every mapped byte has a stored
value, so a load fails exactly when the `n` bytes may not be read: the span passes `2^64`
or a byte lacks read permission. -/
theorem load_eq_none_iff_of_wellFormed {memory : Memory} {pageSize : Nat}
    (wellFormed : memory.WellFormed pageSize) {address : BitVec 64} {n : Nat} :
    load memory address n = none ↔ ¬ memory.Permitted .read address.toNat n :=
  readLE_eq_none_iff_of_wellFormed wellFormed

/-- A load of no byte gives the empty value, at every address and whatever the regions
are. -/
theorem load_zero (memory : Memory) (address : BitVec 64) : load memory address 0 = some 0#0 :=
  Silmaril.Proofs.Machine.AArch64.Memory.load_zero memory address

/-- A load whose `n` bytes would continue past `2^64` fails. For 1, 2, 4 or 8 bytes at a
multiple of that size the hypothesis cannot hold. -/
theorem load_eq_none_of_span_past_limit (memory : Memory) (address : BitVec 64) (n : Nat)
    (past : 2 ^ 64 < address.toNat + n) : load memory address n = none :=
  readLE_eq_none_of_span_past_limit memory .read address n past

/-- A one-byte load is a load of one byte. -/
theorem loadByte_eq_load (memory : Memory) (address : BitVec 64) :
    loadByte memory address = load memory address 1 :=
  rfl

/-- A one-byte load gives `byte` exactly when the byte at `address` may be read and the
memory holds `byte` there. -/
theorem loadByte_eq_some_iff_bytes {memory : Memory} {address : BitVec 64} {byte : BitVec 8} :
    loadByte memory address = some byte ↔
      memory.Permitted .read address.toNat 1 ∧ memory.bytes.get? address.toNat = some byte :=
  Silmaril.Proofs.Machine.AArch64.Memory.loadByte_eq_some_iff_bytes

/-- A one-byte load fails exactly when the checked read of that byte fails.
`load_eq_none_iff_bytes` with `loadByte_eq_load` says when that is: the byte lacks read
permission or has no stored value. -/
theorem loadByte_eq_none_iff {memory : Memory} {address : BitVec 64} :
    loadByte memory address = none ↔ memory.readBytes address.toNat 1 = none :=
  load_eq_none_iff

/-- **When a store succeeds.** A store succeeds exactly when the `n` bytes may be written.
The memory after it has the same regions, and the bytes of `value`, least significant
first, installed at `address`. Read permission and earlier stored values play no part. -/
theorem store_eq_some_iff {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    store memory address n value = some after ↔
      memory.Permitted .write address.toNat n ∧
        after =
          { memory with bytes := Memory.install memory.bytes address.toNat (bytesLE n value) } :=
  Silmaril.Proofs.Machine.AArch64.Memory.store_eq_some_iff

/-- **When a store fails.** A store fails exactly when the `n` bytes may not be written:
the span passes `2^64` or a byte lacks write permission. This needs no well-formedness. -/
theorem store_eq_none_iff {memory : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} :
    store memory address n value = none ↔ ¬ memory.Permitted .write address.toNat n :=
  Silmaril.Proofs.Machine.AArch64.Memory.store_eq_none_iff

/-- **The bytes after a store.** For `i < n`, the byte at `address + i` is bits `8i+7 : 8i`
of the stored value: the least significant byte is at the lowest address. Every other
address holds what it held before, a byte or none. -/
theorem store_get? {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after)
    (location : Nat) :
    after.bytes.get? location =
      if address.toNat ≤ location ∧ location < address.toNat + n then
        some (value.extractLsb' (8 * (location - address.toNat)) 8)
      else memory.bytes.get? location :=
  Silmaril.Proofs.Machine.AArch64.Memory.store_get? stored location

/-- A store of no byte gives the memory back, at every address and whatever the regions
are. -/
theorem store_zero (memory : Memory) (address : BitVec 64) (value : BitVec (8 * 0)) :
    store memory address 0 value = some memory :=
  Silmaril.Proofs.Machine.AArch64.Memory.store_zero memory address value

/-- A store whose `n` bytes would continue past `2^64` fails, and so writes nothing. For 1,
2, 4 or 8 bytes at a multiple of that size the hypothesis cannot hold. -/
theorem store_eq_none_of_span_past_limit (memory : Memory) (address : BitVec 64) (n : Nat)
    (value : BitVec (8 * n)) (past : 2 ^ 64 < address.toNat + n) :
    store memory address n value = none :=
  Silmaril.Proofs.Machine.AArch64.Memory.store_eq_none_of_span_past_limit memory address n
    value past

/-- A store keeps the regions, and with them every permission. -/
theorem store_regions {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after) :
    after.regions = memory.regions :=
  (Memory.writeBytes_writesOnly stored).1

/-- A store keeps the memory well-formed. -/
theorem store_wellFormed {memory after : Memory} {pageSize : Nat} {address : BitVec 64}
    {n : Nat} {value : BitVec (8 * n)} (wellFormed : memory.WellFormed pageSize)
    (stored : store memory address n value = some after) : after.WellFormed pageSize :=
  Memory.writeBytes_wellFormed wellFormed stored

/-- **Load after store, same place.** A load at the address and size of a store gives the
stored value. The bytes must be readable: write permission does not give read permission. -/
theorem load_store_same {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after)
    (readable : memory.Permitted .read address.toNat n) : load after address n = some value :=
  Silmaril.Proofs.Machine.AArch64.Memory.load_store_same stored readable

/-- **Load after store, elsewhere.** A load of `k` bytes that the store did not write gives
what it gave before the store, whether a value or a failure. -/
theorem load_store_of_disjoint {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after)
    (other : BitVec 64) (k : Nat)
    (disjoint : other.toNat + k ≤ address.toNat ∨ address.toNat + n ≤ other.toNat) :
    load after other k = load memory other k :=
  Silmaril.Proofs.Machine.AArch64.Memory.readLE_store_of_disjoint stored .read other k disjoint

/-- **Fetch after store.** A fetch whose four bytes the store did not write gives what it
gave before the store, whether a word or a failure. -/
theorem fetchWord_store_of_disjoint {memory after : Memory} {address : BitVec 64} {n : Nat}
    {value : BitVec (8 * n)} (stored : store memory address n value = some after)
    (pc : BitVec 64) (disjoint : pc.toNat + 4 ≤ address.toNat ∨ address.toNat + n ≤ pc.toNat) :
    fetchWord after pc = fetchWord memory pc :=
  Silmaril.Proofs.Machine.AArch64.Memory.readLE_store_of_disjoint stored .execute pc 4 disjoint

end Silmaril.Machine.AArch64
