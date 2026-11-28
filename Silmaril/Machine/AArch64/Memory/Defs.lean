module

public import Silmaril.Process.Memory

/-!
# AArch64 memory: little-endian bytes, instruction fetch, loads and stores

The memory of the AArch64 machine model is the checked byte memory of
`Silmaril.Process.Memory`: regions with read, write and execute permissions over a table
of bytes. Nothing of that module is redefined here. This layer adds what an A64 access
needs on top of it:

* `bytesLE`, `valueLE`, `ofBytesLE`: the little-endian correspondence between an
  `8n`-bit value and `n` bytes. Byte `i`, the one at `address + i`, is bits `8i+7 : 8i`
  of the value.
* `readLE`: a checked read of `n` bytes as one `8n`-bit value, for a given access kind.
* `fetchWord`: the 32-bit instruction word at an address.
* `wordsBytes`: the bytes of a list of instruction words, for placing code in memory.
* `load`, `loadByte`: the value of `n` bytes, or of one byte, read with read permission.
* `store`: the memory after the `n` bytes of a value are written with write permission.

## Sources

Arm A64 ISA XML 2026-09, file `shared_pseudocode.xml` (line numbers are of that file
unless another file is named), and Arm ARM DDI 0487 M.d.

* `Mem{size}` accessor, lines 16651-16863. For a load or store of one general-purpose
  register under the assumptions below, two of its branches remain (the others are for
  pairs, SIMD, SVE and later features). With the access aligned, the getter is
  `value = AArch64_MemSingle{size}(address, accdesc, aligned);` (16714-16715). Otherwise
  it reads byte by byte: `value[7:0] = AArch64_MemSingle{8}(address, accdesc, aligned);`
  (16738), then, for `i = 1 to bytes-1`,
  `value[i*:8] = AArch64_MemSingle{8}(byteaddress, accdesc, aligned);` with
  `byteaddress = AddressIncrement(address, i, accdesc)` (16748-16751). The setter writes
  the same bytes to the same addresses (16822-16823, 16845-16859). The value is
  byte-reversed only `if BigEndian(accdesc.acctype)` (16755-16757, setter 16781-16783),
  which at EL0 is `SCTLR_ELx().E0E != '0'` (41274-41275).
* `AArch64_MemSingle` accessor, lines 16101-16146: "Perform an atomic, little-endian read
  of 'size' bits." (16106). Without `FEAT_LSE2` it is only reached with an aligned address:
  `assert IsAlignedSize(address, bytes);` (16169, in `AArch64_MemSingleRead`).
* Instruction fetch: "A64 instructions have a fixed length of 32 bits and are always
  little-endian." (Arm ARM B2.9.2, page B2-316). "Instruction fetches would call
  AArch64_MemSingle directly." (comment in `Mem`, 16656).
* Permission for a fetch: `AArch64_S1CheckPermissions`, the `AccessType_IFETCH` branch
  (26476-26488). Its test that applies here is `elsif s1perms.x == '0'` (26486). Its other
  two tests are for permission overlays and for Device memory, which are not modelled. It
  has no read check.
* PC alignment: `AArch64_CheckPCAlignment`, lines 11346-11353.
* Loads on the instruction pages: `let data : bits(8) = Mem{8}(address, accdesc);`
  (`ldrb_imm.xml:320`) and `let data : bits(datasize) = Mem{datasize}(address, accdesc);`
  (`ldr_imm_gen.xml:395`, with `datasize = 8 << scale` at 358). The access descriptor is
  made by `CreateAccDescGPR(MemOp_LOAD, …)` (`ldrb_imm.xml:306`, `ldr_imm_gen.xml:381`).
* Stores on the instruction pages: `Mem{8}(address, accdesc) = data;` (`strb_imm.xml:324`)
  and `Mem{datasize}(address, accdesc) = data;` (`str_imm_gen.xml:395`, with
  `datasize = 8 << scale` at 352). The access descriptor is made by
  `CreateAccDescGPR(MemOp_STORE, …)` (`strb_imm.xml:303`, `str_imm_gen.xml:374`).
* Permission for a load or a store: `AArch64_S1CheckPermissions`. A read faults on
  `elsif accdesc.read && s1perms.r == '0'` (26560) and a write on
  `elsif accdesc.write && s1perms.w == '0'` (26563). The two tests before them (26552,
  26556) are for permission overlays, and the two after them (26566, 26571) are for tag
  accesses and for the dirty state; none of these is modelled. `CreateAccDescGPR` sets
  `accdesc.read = memop == MemOp_LOAD` and `accdesc.write = memop == MemOp_STORE`
  (41702-41703), so a store is checked as a write only.
* Whether an unaligned data access faults: `AArch64_UnalignedAccessFaults`, lines
  16529-16558, with `AlignmentEnforced`, lines 41227-41240.
* Unaligned accesses: without `FEAT_LSE2` "the access is not guaranteed to be single-copy
  atomic except at the byte access level" (Arm ARM B2.8.2.1.1, page B2-312), and "An
  operation that is not single-copy atomic above the byte level can abort on any memory
  access that it makes and can abort on more than one access." (Note at the end of
  B2.8.2.1.3, page B2-314).
* `AddressIncrement`, lines 43870-43884: `var result : bits(64) = base + increment;`
  (43877).
* The top of the address space: "Where an instruction accesses a sequential set of bytes
  that crosses the 0xFFFF_FFFF_FFFF_FFFF boundary when tagged addresses are not used, or
  the 0xXXFF_FFFF_FFFF_FFFF boundary when tagged addresses are used, then the virtual
  address accessed for the bytes above this boundary is UNKNOWN." (Arm ARM D7.2.1, page
  D7-7640). With tagged addressing disabled, for a load or store that "accesses the bytes
  at 0xFFFF_FFFF_FFFF_FFFF and 0x0000_0000_0000_0000", "the bytes that appear to be from
  0x0000_0000_0000_0000 onwards are accessed at an UNKNOWN address. It is permitted for
  the UNKNOWN address used to be a fixed value such that it always generates an MMU
  fault." (Arm ARM K1.2.9, page K1-16818). The Note there: "Because of Program Counter
  alignment constraints, it is impossible for a PE to fetch an A64 instruction that
  includes both the byte at virtual address 0xFFFF_FFFF_FFFF_FFFF and the byte at virtual
  address 0x0000_0000_0000_0000."
* What a faulting access leaves behind: an exception is precise if the state "is
  consistent with the PE having executed all of the instructions up to but not including
  the point in the instruction stream where the exception was taken from, and none
  afterwards", but for the instruction at that point "the definition of precise also
  permits any of the following". The first of these: "For synchronous Data Abort and
  Watchpoint exceptions that are taken to AArch64 state generated by an instruction that
  performs more than one single-copy atomic memory access, the values in registers or
  memory affected by the instruction can be UNKNOWN, if all of the following apply:",
  namely "The accesses affecting those registers or memory locations do not, themselves,
  generate exceptions or debug events." and "The registers are not involved in the
  calculation of the memory address used by the instruction." The second says of a load
  "that does not load the base address register or the offset register" that "the
  destination registers become UNKNOWN". (Arm ARM D1.4.1.4, R_TNVSL, page D1-7214.)
* Stage 2 permissions: "Software executing at EL2 can assign a write-only permission to a
  memory region." (Arm ARM D8.4.3, I_JYHLR, page D8-7773).

## Assumptions

Armv8.0 with no later features, execution at EL0, no stage 2 translation, no tagged
addresses, and little-endian data (`SCTLR_EL1.E0E = 0`). So `BigEndian` is false and no
byte reversal is modelled, and with the same bytes at the same addresses the aligned and
the byte-by-byte paths of `Mem` give one value: the little-endian value of the `n` bytes at
`address`, …, `address + n - 1`.

## What this layer does and does not do

* **No PC alignment check in `fetchWord`.** Arm checks the PC before it fetches
  (`AArch64_CheckPCAlignment`). A caller that models an instruction fetch must make that
  check first and only then call `fetchWord`; `fetchWord` itself reads at any address. At
  an address that is not a multiple of 4 it has no Arm counterpart, since
  `AArch64_MemSingle` is not reached there.
* **Execute permission only.** `fetchWord` needs execute permission on each of its four
  bytes and no read permission, as in the `AccessType_IFETCH` branch.
* **Read permission for a load, write permission for a store.** `load` needs read
  permission on each of its bytes, and `store` needs write permission on each of its
  bytes. A store does not need its bytes to be readable, and it does not need them to
  hold a value already.
* **Permissions are taken as given.** The permission bits of a region are the effective
  permissions of its bytes: what `AArch64_S1CheckPermissions` tests as `s1perms.r`,
  `s1perms.w` and `s1perms.x`. How a system arrives at them is not modelled: the
  translation tables and their `AP` bits (`AArch64_S1DirectBasePermissions`, 26646-26744),
  `SCTLR_EL1.WXN` (read at 30244), which removes execute permission from writable memory
  (`uwxn = walkparams.wxn AND uw AND ux;` at 26683, then
  `s1perms.x  = s1perms.x AND NOT(s1perms.wxn);` at 26619), permission overlays, and Device
  memory. So the model allows combinations that stage 1 of Armv8.0 cannot produce at EL0.
  Write-only memory is one: at stage 1 the `AP` bits give EL0 write permission only
  together with read permission (26664-26669), the hierarchical bits remove the read
  permission only together with the write permission (26672-26677), and EL0 gets these
  bits (26719). Stage 2 can produce it: "Software executing at EL2 can assign a write-only
  permission to a memory region." (I_JYHLR, cited above). Stage 2 translation is not
  modelled either.
* **A store is all-or-nothing here.** `store` checks the whole span first and writes only
  if every byte may be written. A store that fails gives `none`: no byte is written, and
  the caller still has the memory from before. Arm does not promise this for every store.
  At an aligned address it makes one access, translated and checked before the write
  (`AArch64_MemSingleWrite`, 16307-16312, write at 16353). But its byte-by-byte store
  checks and writes one byte after the other (16845-16859), and such an access "can abort
  on any memory access that it makes" (the Note cited above). What memory holds after
  such a fault is governed by the definition of a precise exception (R_TNVSL, cited
  above): for an instruction with more than one single-copy atomic access, the memory it
  affects "can be UNKNOWN" where the access to that location did not itself fault. So the
  order of the pseudocode and this rule together allow that an unaligned store which
  faults on a later byte has already written the earlier bytes, and they do not fix what
  those bytes then hold. Leaving memory unchanged on a fault is the contract this model
  chooses. It is not a claim that a store is atomic on hardware. The same rule lets the
  destination register of a faulting load become UNKNOWN; that is for the instruction
  semantics, not for this layer.
* **No data alignment check.** `readLE`, `load` and `store` access any address. Whether an
  unaligned data access faults (`AArch64_UnalignedAccessFaults`) is for the instruction
  semantics.
* **A span passing `2^64` is refused.** The reused memory checks
  `address + n ≤ 2^64` (`Memory.checkSpan`), so an access whose bytes would continue past
  the top of the address space fails. This holds for fetches, loads and stores alike; such
  a store writes nothing. Arm permits this behaviour. The pseudocode alone would go on at
  address 0, since `AddressIncrement` adds on 64 bits (43877). But the Arm ARM does not
  fix the address of the bytes above the boundary: it "is UNKNOWN" (D7.2.1), and "It is
  permitted for the UNKNOWN address used to be a fixed value such that it always generates
  an MMU fault." (K1.2.9; both cited above). To fail is that permitted choice. An access
  of 1, 2, 4 or 8 bytes at an address that is a multiple of its size ends at or below
  `2^64`, so this concerns unaligned accesses only. For a fetch it concerns only an
  address that is not a multiple of 4, which Arm's PC alignment check excludes (the Note
  in K1.2.9).
* **A mapped byte with no stored value makes a read fail.** The reused memory keeps
  permissions and bytes apart, and `Memory.readBacking` gives `none` for an address that
  has no byte, even if a region maps it. `Memory.WellFormed` excludes that case. A store
  has no such condition: it gives a value to every byte it writes.
* **Sizes.** Arm's `Mem{size}` takes 8, 16, 32, …, 256 bits. Here `n` is any number of
  bytes; the machine model uses 1, 4 and 8. With `n = 0` no byte is accessed: a load
  gives the empty value and a store gives the memory back, at every address.

## Region dependency

`Silmaril.Process` is not among the declared `deps` of region `Machine` in
`regions.toml`. Importing `Silmaril.Process.Memory` here is a stated exception, agreed
with the maintainers, so that the machine model reuses the existing checked memory instead
of copying it.

This is a handwritten model. It follows the Arm text; it makes no claim of equivalence
with the ASL or with any other model. `Silmaril.Machine.AArch64.Memory.Thms` proves that
`bytesLE` and `ofBytesLE` are inverse, and says when `readLE`, `fetchWord`, `load` and
`store` succeed. It also proves which byte a store puts at each address, that a store keeps
the regions and well-formedness, that a load after a store at the same address gives the
stored value, and that loads and fetches of bytes the store did not write are unchanged.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64

open Silmaril.Process (Memory Byte Access)

/-! ## Little-endian bytes -/

/-- The `n` bytes of `value`, least significant first: element `i` is bits `8i+7 : 8i`.

This is the order in which Arm's `Mem` setter stores a value: byte `i` goes to
`address + i`, as in `AArch64_MemSingle{8}(byteaddress, accdesc, aligned) = value[i*:8];`
with `byteaddress = AddressIncrement(address, i, accdesc)`. -/
def bytesLE (n : Nat) (value : BitVec (8 * n)) : List Byte :=
  (List.range n).map fun i => value.extractLsb' (8 * i) 8

/-- The number denoted by bytes given least significant first: byte `i` counts
`256 ^ i` times its value. -/
def valueLE : List Byte → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * valueLE rest

/-- The `8n`-bit value of bytes given least significant first.

For a list of exactly `n` bytes, bits `8i+7 : 8i` of the result are byte `i`
(`bytesLE_ofBytesLE`). This is how Arm's `Mem` getter builds a value from the byte at each
`address + i`: `value[i*:8] = AArch64_MemSingle{8}(byteaddress, accdesc, aligned);`.
Every use in this module passes exactly `n` bytes. For other lengths the definition still
gives a value: bytes beyond the first `n` are dropped, and missing high bytes are zero. -/
def ofBytesLE (n : Nat) (bytes : List Byte) : BitVec (8 * n) :=
  BitVec.ofNat (8 * n) (valueLE bytes)

/-! ## Checked little-endian reads -/

/-- A checked little-endian read of `n` bytes with the given access kind. `none` exactly
when `Memory.readWith access address.toNat n` is `none`.

The reused memory checks the whole span first: every byte from `address` to
`address + n - 1` must lie below `2^64` and in a region that allows `access`. It then
needs a stored byte at each address. The bytes read are put together least significant
first. There is no alignment check. -/
def readLE (memory : Memory) (access : Access) (address : BitVec 64) (n : Nat) :
    Option (BitVec (8 * n)) :=
  (memory.readWith access address.toNat n).map (ofBytesLE n)

/-! ## Instruction fetch -/

/-- The 32-bit instruction word at `address`: 4 bytes, execute permission. No alignment check.

"A64 instructions have a fixed length of 32 bits and are always little-endian" (Arm ARM
B2.9.2), so the byte at `address` is bits `7:0` of the word. The four bytes need execute
permission and no read permission. Arm checks that the PC is a multiple of 4 before the
fetch; that check belongs to the caller. -/
def fetchWord (memory : Memory) (address : BitVec 64) : Option (BitVec 32) :=
  readLE memory .execute address 4

/-- The bytes of a list of instruction words, in memory order: the four bytes of the
first word, least significant first, then those of the second word, and so on. Installing
them at a base address puts word `i` at `base + 4 * i` (`fetchWord_installWords`). -/
def wordsBytes (words : List (BitVec 32)) : List Byte :=
  words.flatMap (bytesLE 4)

/-! ## Loads and stores -/

/-- A little-endian load of `n` bytes: read permission on every byte.

The instruction pages read memory with `let data : bits(8) = Mem{8}(address, accdesc);`
(`ldrb_imm.xml:320`) and `let data : bits(datasize) = Mem{datasize}(address, accdesc);`
(`ldr_imm_gen.xml:395`), the access being a `MemOp_LOAD` (`ldrb_imm.xml:306`,
`ldr_imm_gen.xml:381`). The `Mem` getter takes the byte at `address + i` as bits
`8i+7 : 8i` of the value. Byte by byte it says so directly
(`shared_pseudocode.xml:16738-16751`), and this is the little-endian order: `Mem` reverses
the bytes only for a big-endian access (16755-16757). For an aligned address it makes one
access with `AArch64_MemSingle` (16714-16715), which is "an atomic, little-endian read of
'size' bits" (16106). A read faults on `accdesc.read && s1perms.r == '0'`
(`shared_pseudocode.xml:26560`).

The result is `none` if the span passes `2^64`, if a byte lacks read permission, or if a
byte has no stored value. There is no alignment check. -/
def load (memory : Memory) (address : BitVec 64) (n : Nat) : Option (BitVec (8 * n)) :=
  readLE memory .read address n

/-- A one-byte load: `load` of one byte, as a plain 8-bit value.

This is `let data : bits(8) = Mem{8}(address, accdesc);` (`ldrb_imm.xml:320`). Every
address is aligned for one byte, so `Mem` takes its aligned path
(`shared_pseudocode.xml:16714-16715`). -/
def loadByte (memory : Memory) (address : BitVec 64) : Option (BitVec 8) :=
  load memory address 1

/-- A little-endian store of `n` bytes: write permission on every byte; `none` changes
nothing.

The instruction pages write memory with `Mem{8}(address, accdesc) = data;`
(`strb_imm.xml:324`) and `Mem{datasize}(address, accdesc) = data;`
(`str_imm_gen.xml:395`), the access being a `MemOp_STORE` (`strb_imm.xml:303`,
`str_imm_gen.xml:374`). The `Mem` setter puts bits `8i+7 : 8i` of the value at
`address + i` (`shared_pseudocode.xml:16822-16823` for an aligned address, 16845-16859
byte by byte), and a write faults on `accdesc.write && s1perms.w == '0'`
(`shared_pseudocode.xml:26563`).

The reused memory checks the whole span first (`Memory.writeBytes`): every byte from
`address` to `address + n - 1` must lie below `2^64` and in a region that allows writing.
Only then are the `n` bytes of `value` written, least significant first. Read permission
is not needed, and the bytes need not hold a value before. If the check fails, the result
is `none` and no byte is written. Arm's byte-by-byte store can instead fault after it has
written some bytes: see "A store is all-or-nothing here" in the module documentation.
There is no alignment check. -/
def store (memory : Memory) (address : BitVec 64) (n : Nat) (value : BitVec (8 * n)) :
    Option Memory :=
  memory.writeBytes address.toNat (bytesLE n value)

end Silmaril.Machine.AArch64
