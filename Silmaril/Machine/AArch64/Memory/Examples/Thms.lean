module

public import Silmaril.Machine.AArch64.Memory.Examples.Defs
public import Silmaril.Machine.AArch64.Memory.Image.Thms

/-!
# AArch64 memory: worked examples

Facts about the example memories of `Silmaril.Machine.AArch64.Memory.Examples.Defs`, with
expected values worked out by hand from the bytes of the images. They are evidence for
`fetchWord`, `load`, `loadByte` and `store`: byte order, permissions, the ends of a region,
regions that touch, bytes without a value, the top of the address space, and what a store
changes.

Every fact is checked by the kernel. The proofs are the recipe of
`Silmaril.Machine.AArch64.Memory.Image.Thms`,

```
  simp only [aarch64_image]
  decide
```

its one-equation form, or one of the two forms given there for a store with its image
written out. A fact about lists alone needs only `decide`.

A failure is only evidence for the cause it names if no other cause is present. So where a
read is said to fail because of a permission, of the end of a region or of the top of the
address space, the image does hold the bytes, and a statement next to it says so. Where a
fetch is said to fail because a byte has no value, a statement says that it is permitted.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64.Memory.Examples

open Silmaril.Process (Memory Byte Access Region)

/-! ## Lookup in a bare image -/

/-- The rules of `Image.get?` on small images. An earlier block hides a later one where
they overlap, and only there. With the same base twice, the first block wins. An empty
block hides nothing. A block holds nothing below its base. -/
theorem lookup_rules :
    Image.get? [(0, [0x01, 0x02]), (1, [0x09, 0x0A])] 1 = some 0x02 ∧
      Image.get? [(0, [0x01, 0x02]), (1, [0x09, 0x0A])] 2 = some 0x0A ∧
      Image.get? [(5, [0x01]), (5, [0x02])] 5 = some 0x01 ∧
      Image.get? [(5, []), (5, [0x02])] 5 = some 0x02 ∧
      Image.get? [(3, [0x01])] 2 = none := by
  decide

/-! ## Byte order of a fetch -/

/-- The bytes `11 22 33 44` at `0x1000` are the word `0x44332211`: the byte at the lowest
address is the least significant. Proved with the one-equation form of the recipe: one
rewriting step with a bridge equation, then `decide`. -/
theorem fetch_first_word : fetchWord memory 0x1000#64 = some 0x44332211#32 := by
  rw [Image.fetchWord_memory]
  decide

/-- The same fetch is not the big-endian reading `0x11223344`. -/
theorem fetch_first_word_ne : fetchWord memory 0x1000#64 ≠ some 0x11223344#32 := by
  simp only [aarch64_image]
  decide

/-- The bytes `00 04 00 91` at `0x1004` are `0x91000400`, the word of `ADD X0, X0, #1`. -/
theorem fetch_add : fetchWord memory 0x1004#64 = some 0x91000400#32 := by
  simp only [aarch64_image]
  decide

/-- The reused memory itself, through the bridge `Image.readWith_memory`: the four bytes at
`0x1000` in address order, read with execute permission. -/
theorem readWith_first_word :
    memory.readWith .execute 0x1000 4 = some [0x11, 0x22, 0x33, 0x44] := by
  rw [Image.readWith_memory]
  decide

/-- The reused memory's own reads, by the recipe: four bytes of the read-only region with
`readBytes`, four bytes of the executable region with `fetchBytes`, both in address order.
`readBytes` on the executable region fails. -/
theorem readBytes_and_fetchBytes :
    memory.readBytes 0x2000 4 = some [0x11, 0x22, 0x33, 0x44] ∧
      memory.fetchBytes 0x1004 4 = some [0x00, 0x04, 0x00, 0x91] ∧
      memory.readBytes 0x1000 4 = none := by
  simp only [aarch64_image]
  decide

/-! ## The nine combinations of access and permission

Each access at the first four bytes of the execute-only, the read-only and the write-only
region. Three succeed: a fetch where execution is allowed, a load where reading is allowed,
a store where writing is allowed. The other six fail. Every region holds bytes, so a failed
read fails because of the permission. -/

/-- A fetch succeeds on the execute-only region and fails on the other two. -/
theorem fetch_permissions :
    fetchWord memory 0x1000#64 = some 0x44332211#32 ∧
      fetchWord memory 0x2000#64 = none ∧ fetchWord memory 0x3000#64 = none := by
  simp only [aarch64_image]
  decide

/-- A load succeeds on the read-only region and fails on the other two. -/
theorem load_permissions :
    load memory 0x1000#64 4 = none ∧
      load memory 0x2000#64 4 = some 0x44332211#32 ∧ load memory 0x3000#64 4 = none := by
  simp only [aarch64_image]
  decide

/-- A store succeeds on the write-only region and fails on the other two. -/
theorem store_permissions :
    store memory 0x1000#64 4 0xAABBCCDD#32 = none ∧
      store memory 0x2000#64 4 0xAABBCCDD#32 = none ∧
        (store memory 0x3000#64 4 0xAABBCCDD#32).isSome = true := by
  simp only [aarch64_image]
  decide

/-- The image holds the first four bytes of each of the three regions. So the four reads
that fail above, two fetches and two loads, fail because of the permission. -/
theorem image_read_three_regions :
    Image.read image 0x1000 4 = some [0x11, 0x22, 0x33, 0x44] ∧
      Image.read image 0x2000 4 = some [0x11, 0x22, 0x33, 0x44] ∧
      Image.read image 0x3000 4 = some [0x30, 0x31, 0x32, 0x33] := by
  decide

/-! ## The ends of a region

The executable region is `0x1000`, …, `0x100F`. The image holds four more bytes on each
side, `D0 D1 D2 D3` before it and `E0 E1 E2 E3` after it, in no region. So each failure
below is caused by the end of the region, and not by a missing byte. -/

/-- A fetch of the last four bytes of the executable region, `C0 03 5F D6` at `0x100C`,
gives `0xD65F03C0`. -/
theorem fetch_last_word : fetchWord memory 0x100C#64 = some 0xD65F03C0#32 := by
  simp only [aarch64_image]
  decide

/-- Two bytes later the fetch fails: the bytes at `0x1010` and `0x1011` are in no region. -/
theorem fetch_past_end : fetchWord memory 0x100E#64 = none := by
  simp only [aarch64_image]
  decide

/-- The image does hold those four bytes, so the fetch at `0x100E` fails because of the
regions and not because a byte is missing. -/
theorem image_read_past_end : Image.read image 0x100E 4 = some [0x5F, 0xD6, 0xE0, 0xE1] := by
  decide

/-- One byte after the last full word, at `0x100D`, the fetch fails already: its last byte,
at `0x1010`, is in no region. -/
theorem fetch_one_past_end : fetchWord memory 0x100D#64 = none := by
  simp only [aarch64_image]
  decide

/-- A fetch that starts before the region fails, with three bytes before it (`0x0FFD`) and
with one (`0x0FFF`). The fetch at `0x1000` succeeds (`fetch_first_word`). -/
theorem fetch_before_start :
    fetchWord memory 0x0FFD#64 = none ∧ fetchWord memory 0x0FFF#64 = none := by
  simp only [aarch64_image]
  decide

/-- The image holds the four bytes of each of these three fetches too, so they fail because
of the regions and not because a byte is missing. -/
theorem image_read_around_region :
    Image.read image 0x100D 4 = some [0x03, 0x5F, 0xD6, 0xE0] ∧
      Image.read image 0x0FFD 4 = some [0xD1, 0xD2, 0xD3, 0x11] ∧
      Image.read image 0x0FFF 4 = some [0xD3, 0x11, 0x22, 0x33] := by
  decide

/-! ## Regions that touch

`adjacent` has read-only regions at `0x6000` and `0x6004` and a write-only region at
`0x6008`, four bytes each, holding `60 61 … 6B`. An access may go across regions if every
byte has the permission. -/

/-- A load of `62 63 64 65` goes across the two read-only regions and gives `0x65646362`. -/
theorem load_across_readable_regions : load adjacent 0x6002#64 4 = some 0x65646362#32 := by
  simp only [aarch64_image]
  decide

/-- The last load that stays in the read-only regions, `64 65 66 67` at `0x6004`, gives
`0x67666564`. One byte later the load reaches the write-only region and fails, and so does
the load at `0x6006`, with two bytes in each region. -/
theorem load_into_writeOnly_region :
    load adjacent 0x6004#64 4 = some 0x67666564#32 ∧
      load adjacent 0x6005#64 4 = none ∧ load adjacent 0x6006#64 4 = none := by
  simp only [aarch64_image]
  decide

/-- The image holds the bytes of the two failing loads. -/
theorem adjacentImage_read :
    Image.read adjacentImage 0x6005 4 = some [0x65, 0x66, 0x67, 0x68] ∧
      Image.read adjacentImage 0x6006 4 = some [0x66, 0x67, 0x68, 0x69] := by
  decide

/-! ## Loads of one, four and eight bytes

The read-only region starts with `11 22 33 44 55 66 77 88`. -/

/-- One byte: `0x11`. -/
theorem load_byte : loadByte memory 0x2000#64 = some 0x11#8 := by
  simp only [aarch64_image]
  decide

/-- `load` of one byte gives the same. -/
theorem load_one : load memory 0x2000#64 1 = some 0x11#8 := by
  simp only [aarch64_image]
  decide

/-- Four bytes: `0x44332211`. -/
theorem load_four : load memory 0x2000#64 4 = some 0x44332211#32 := by
  simp only [aarch64_image]
  decide

/-- Eight bytes: `0x8877665544332211`. -/
theorem load_eight : load memory 0x2000#64 8 = some 0x8877665544332211#64 := by
  simp only [aarch64_image]
  decide

/-- Four bytes at the unaligned address `0x2001`, `22 33 44 55`: `0x55443322`. This layer
checks no alignment. -/
theorem load_unaligned : load memory 0x2001#64 4 = some 0x55443322#32 := by
  simp only [aarch64_image]
  decide

/-! ## Stores

The read-and-write region holds `40 41 42 43 44 45 46 47 48 …` from `0x4000`. The examples
store `0xAABBCCDD` at `0x4004`, which writes `DD CC BB AA` to `0x4004`, …, `0x4007`. -/

/-- A load at the address and size of the store gives the stored value. -/
theorem store_then_load :
    (store memory 0x4004#64 4 0xAABBCCDD#32).bind (fun m => load m 0x4004#64 4) =
      some 0xAABBCCDD#32 := by
  simp only [aarch64_image]
  decide

/-- Byte order of a store: the least significant byte `DD` goes to the lowest address
`0x4004`, the most significant byte `AA` to `0x4007`. -/
theorem store_byte_order :
    (store memory 0x4004#64 4 0xAABBCCDD#32).bind (fun m => loadByte m 0x4004#64) =
        some 0xDD#8 ∧
      (store memory 0x4004#64 4 0xAABBCCDD#32).bind (fun m => loadByte m 0x4007#64) =
        some 0xAA#8 := by
  simp only [aarch64_image]
  decide

/-- The bytes next to the stored span, at `0x4003` and at `0x4008`, hold `0x43` and `0x48`
before the store. -/
theorem neighbours_before_store :
    loadByte memory 0x4003#64 = some 0x43#8 ∧ loadByte memory 0x4008#64 = some 0x48#8 := by
  simp only [aarch64_image]
  decide

/-- They hold the same after the store. -/
theorem neighbours_after_store :
    (store memory 0x4004#64 4 0xAABBCCDD#32).bind (fun m => loadByte m 0x4003#64) =
        some 0x43#8 ∧
      (store memory 0x4004#64 4 0xAABBCCDD#32).bind (fun m => loadByte m 0x4008#64) =
        some 0x48#8 := by
  simp only [aarch64_image]
  decide

/-- Eight bytes from `0x4000` after the store: the old bytes `40 41 42 43`, then the stored
bytes `DD CC BB AA`. The new block hides the old one only where it covers it. -/
theorem store_then_load_around :
    (store memory 0x4004#64 4 0xAABBCCDD#32).bind (fun m => load m 0x4000#64 8) =
      some 0xAABBCCDD43424140#64 := by
  simp only [aarch64_image]
  decide

/-- A store to the write-only region succeeds, and a load of what was stored fails: the
result is `some none`, a memory after the store and no value from the load. Write
permission does not give read permission. -/
theorem store_writeOnly_then_load :
    (store memory 0x3000#64 4 0xAABBCCDD#32).map (fun m => load m 0x3000#64 4) = some none := by
  simp only [aarch64_image]
  decide

/-! ## Unmapped addresses -/

/-- At `0x5000` there is no region and no byte: every access fails. -/
theorem unmapped :
    fetchWord memory 0x5000#64 = none ∧ load memory 0x5000#64 4 = none ∧
      store memory 0x5000#64 4 0xAABBCCDD#32 = none := by
  simp only [aarch64_image]
  decide

/-- At `0x1010` the image holds bytes, but no region maps them: a load fails all the same. -/
theorem unmapped_with_bytes :
    load memory 0x1010#64 4 = none ∧
      Image.read image 0x1010 4 = some [0xE0, 0xE1, 0xE2, 0xE3] := by
  simp only [aarch64_image]
  decide

/-! ## Several steps -/

/-- Two stores, then a load and a fetch, in `do` notation. The stores write `DD CC BB AA`
at `0x4000` and `44 33 22 11` at `0x4004`, so the eight bytes at `0x4000` are
`0x11223344AABBCCDD`. The fetch at `0x1004` is not affected: `0x91000400`. -/
theorem two_stores_then_load_and_fetch :
    (do
      let m ← store memory 0x4000#64 4 0xAABBCCDD#32
      let m ← store m 0x4004#64 4 0x11223344#32
      let value ← load m 0x4000#64 8
      let word ← fetchWord m 0x1004#64
      pure (value, word)) = some (0x11223344AABBCCDD#64, 0x91000400#32) := by
  simp only [aarch64_image]
  decide

/-- Two stores that overlap. The first writes `DD CC BB AA` at `0x4000`, …, `0x4003`. The
second writes `44 33 22 11` at `0x4002`, …, `0x4005`. The eight bytes at `0x4000` are then
`DD CC 44 33 22 11 46 47`, which is `0x474611223344CCDD`: the later store wins where the
two overlap, and the bytes `46 47` are the old ones. -/
theorem overlapping_stores :
    ((store memory 0x4000#64 4 0xAABBCCDD#32).bind fun m =>
      (store m 0x4002#64 4 0x11223344#32).bind fun m => load m 0x4000#64 8) =
      some 0x474611223344CCDD#64 := by
  simp only [aarch64_image]
  decide

/-- Eight bytes stored at the unaligned address `0x4003`. The store writes
`88 77 66 55 44 33 22 11` to `0x4003`, …, `0x400A`, so the region then holds
`40 41 42 88 77 66 55 44 33 22 11 4B 4C 4D 4E 4F`. A load of eight bytes at `0x4003` gives
the stored value. The two aligned loads that the store straddles give
`40 41 42 88 77 66 55 44` at `0x4000` and `33 22 11 4B 4C 4D 4E 4F` at `0x4008`. -/
theorem store_eight_unaligned :
    (store memory 0x4003#64 8 0x1122334455667788#64).bind (fun m => load m 0x4003#64 8) =
        some 0x1122334455667788#64 ∧
      (store memory 0x4003#64 8 0x1122334455667788#64).bind (fun m => load m 0x4000#64 8) =
        some 0x4455667788424140#64 ∧
      (store memory 0x4003#64 8 0x1122334455667788#64).bind (fun m => load m 0x4008#64 8) =
        some 0x4F4E4D4C4B112233#64 := by
  simp only [aarch64_image]
  decide

/-- The reused memory's own write and read, by the recipe. `DD CC` written at `0x4004` and
`0x4005`; the four bytes from `0x4003` are then `43 DD CC 46`. -/
theorem writeBytes_then_readBytes :
    (memory.writeBytes 0x4004 [0xDD, 0xCC]).bind (fun m => m.readBytes 0x4003 4) =
      some [0x43, 0xDD, 0xCC, 0x46] := by
  simp only [aarch64_image]
  decide

/-! ## A store with its image written out -/

/-- The memory after the store, as an image: the stored bytes, least significant first, in
front of the old image. -/
theorem store_image :
    store memory 0x4004#64 4 0xAABBCCDD#32 =
      some (Image.memory regions ((0x4004, [0xDD, 0xCC, 0xBB, 0xAA]) :: image)) :=
  Image.store_memory_eq_some (by decide)

/-- The same store as a hypothesis: whatever memory it gives, a load there gives the stored
value. -/
theorem load_of_store (after : Memory)
    (stored : store memory 0x4004#64 4 0xAABBCCDD#32 = some after) :
    load after 0x4004#64 4 = some 0xAABBCCDD#32 := by
  obtain ⟨-, rfl⟩ := Image.store_memory_eq_some_iff.mp stored
  simp only [aarch64_image]
  decide

/-! ## A tiny memory: bytes without a value

One region of eight bytes with every permission. The image gives a value to the first four
bytes only. -/

/-- A successful read, proved by one rewriting step with a bridge equation and `decide`. -/
theorem tiny_fetch : fetchWord tiny 0#64 = some 0x44332211#32 := by
  rw [Image.fetchWord_memory]
  decide

/-- A fetch fails where a byte has no value, although the region allows it: at 4 all four
bytes are missing, at 2 the last two are. This failure is found by the list lookup; the
permission check passes. -/
theorem tiny_fetch_without_value : fetchWord tiny 4#64 = none ∧ fetchWord tiny 2#64 = none := by
  simp only [aarch64_image]
  decide

/-- Both of these fetches are permitted, so they fail only because bytes have no value. -/
theorem tiny_fetch_permitted : tiny.Permitted .execute 4 4 ∧ tiny.Permitted .execute 2 4 := by
  decide

/-- A store gives the bytes a value: after it the fetch at 4 succeeds. -/
theorem tiny_store_then_fetch :
    (store tiny 4#64 4 0x91000400#32).bind (fun m => fetchWord m 4#64) = some 0x91000400#32 := by
  simp only [aarch64_image]
  decide

/-! ## The top of the address space

The reused memory refuses a span that passes `2^64`. Arm permits that: the Arm ARM leaves
the address of the bytes above the boundary UNKNOWN and allows it to be one that always
faults (see "A span passing `2^64` is refused" in the module documentation of
`Silmaril.Machine.AArch64.Memory.Defs`). The region and the image of `top` continue past
`2^64` as natural numbers (`top_bytes_and_region`), so each failure below is caused by the
limit alone. The failing fetches are at addresses that are not multiples of 4: at a
multiple of 4 a fetch cannot pass `2^64`. -/

/-- The last four bytes below `2^64`, `FC FD FE FF`, are fetched as `0xFFFEFDFC`. -/
theorem top_fetch_last_word : fetchWord top 0xFFFFFFFFFFFFFFFC#64 = some 0xFFFEFDFC#32 := by
  simp only [aarch64_image]
  decide

/-- Two bytes later the span would pass `2^64`, and the fetch is refused, although the
region and the image both continue. -/
theorem top_fetch_past_limit : fetchWord top 0xFFFFFFFFFFFFFFFE#64 = none := by
  simp only [aarch64_image]
  decide

/-- One byte after the last word, at `0xFFFFFFFFFFFFFFFD`, the fetch is refused already: it
would need the byte at `2^64`. -/
theorem top_fetch_one_past_limit : fetchWord top 0xFFFFFFFFFFFFFFFD#64 = none := by
  simp only [aarch64_image]
  decide

/-- A load of the last four bytes below `2^64` gives `0xFFFEFDFC`. A load of eight bytes at
the same address would need four bytes past `2^64`, and is refused. -/
theorem top_load_four_and_eight :
    load top 0xFFFFFFFFFFFFFFFC#64 4 = some 0xFFFEFDFC#32 ∧
      load top 0xFFFFFFFFFFFFFFFC#64 8 = none := by
  simp only [aarch64_image]
  decide

/-- The image holds the bytes of the two failing fetches and of the failing load. The
region, which is one range, allows execution at the natural numbers `2^64` and `2^64 + 1`,
and reading at `2^64 + 3`, the last byte the load of eight bytes would need. So the
failures above are caused by the limit alone. -/
theorem top_bytes_and_region :
    Image.read topImage 0xFFFFFFFFFFFFFFFD 4 = some [0xFD, 0xFE, 0xFF, 0x00] ∧
      Image.read topImage 0xFFFFFFFFFFFFFFFE 4 = some [0xFE, 0xFF, 0x00, 0x01] ∧
      Image.read topImage 0xFFFFFFFFFFFFFFFC 8 =
        some [0xFC, 0xFD, 0xFE, 0xFF, 0x00, 0x01, 0x02, 0x03] ∧
      top.permits .execute 0x10000000000000000 = true ∧
      top.permits .execute 0x10000000000000001 = true ∧
      top.permits .read 0x10000000000000003 = true := by
  decide

end Silmaril.Machine.AArch64.Memory.Examples
