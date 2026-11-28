module

public import Silmaril.Machine.AArch64.Memory.Defs
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# AArch64 memory images: memory as lists, so that the kernel can check concrete examples

## Why this helper exists

The memory of the machine model is the reused `Silmaril.Process.Memory`. It keeps its bytes
in a hash map (`Std.ExtHashMap Nat Byte`). Lean's kernel cannot evaluate a lookup in that
hash map. So `decide` cannot prove a concrete fact such as
`fetchWord memory 0x1000#64 = some 0x44332211#32`: the permission check evaluates, the byte
lookups do not. Compiled evaluation can test such a fact, and tests in this repository use
it. But a test is not a proof, and proofs by compiled evaluation are not accepted here. So
a concrete example that is to be a theorem needs another route, one that the kernel checks.

This module is that route. It describes the bytes of a memory a second time, as plain lists.
List lookups are something the kernel evaluates. The statements in
`Silmaril.Machine.AArch64.Memory.Image.Thms` say that a memory built from such lists
behaves exactly like the lists, so a fact about the memory becomes a fact about lists, and
`decide` proves it.

## What an image is

An `Image` is a list of blocks. A block `(base, bytes)` puts `bytes[0]` at address `base`,
`bytes[1]` at `base + 1`, and so on. Addresses are natural numbers, as in the reused
memory.

* `Image.bytes image` is the hash map the image denotes: the blocks are installed with
  `Memory.install`, the last block first.
* `Image.get? image address` is the byte at an address, found by walking the list.
* `Image.read image address n` is `n` bytes from an address, found the same way.
* `Image.memory regions image` is the memory with the given regions whose bytes are
  `Image.bytes image`.

## Overlap: an earlier block hides later ones

Blocks may overlap, and the same base may occur twice. Where two blocks cover the same
address, the block nearer the front of the list gives the byte. This makes putting a block
in front of an image the same as writing that block to memory: the image
`(address, block) :: image` denotes the memory after `block` is written at `address`
(`Image.writeBytes_memory`). So a memory stays in image form after a store, and an example
can go through several stores.

An empty block holds no byte and hides nothing.

## Images and regions are independent

An image says which bytes have a value. The regions say which bytes may be accessed. No
condition links the two. A region may cover an address where the image has no byte: a read
there fails, as in the reused memory. The image may have a byte where no region is: no
access reaches it.

## The accesses in list form

`Image.checkedRead` and `Image.checkedStore` are what `readLE` and `store` compute on
`Image.memory regions image`, written with list lookups only: the same permission check,
then `Image.read`, or a new block in front of the image. `Image.readLE_memory`,
`Image.fetchWord_memory`, `Image.load_memory`, `Image.loadByte_memory` and
`Image.store_memory` state this.

## The simp set `aarch64_image`

`aarch64_image` is the set of equations that put an access to an image-backed memory into
list form. `simp only [aarch64_image]` followed by `decide` is the way to check a concrete
example; `Silmaril.Machine.AArch64.Memory.Image.Thms` says how, and
`Silmaril.Machine.AArch64.Memory.Examples.Thms` has worked examples. The equations are
tagged in `Image.Thms`. This module only registers the attribute, because Lean cannot use
an attribute in the module that declares it. A later layer of the machine model can add its
own equations to the set instead of copying a list of lemma names.

## What this is not

This is a tool for stating and checking concrete examples: a few regions, a few bytes, one
expected value. It is not part of the machine semantics. The semantics is defined on
`Memory`, and no definition of the machine model mentions `Image`. Lookup walks the lists,
so the cost grows with the size of the image.
-/

public meta section

/-- The equations that put fetches, loads and stores on `Image.memory regions image`, and
the checked reads and writes of the reused memory on it, into list form, also after one or
more stores. `simp only [aarch64_image]` and then `decide` checks a concrete example. -/
register_simp_attr aarch64_image

end

@[expose] public section

namespace Silmaril.Machine.AArch64

open Silmaril.Process (Memory Byte Access ByteMemory Region)

/-! ## Images -/

/-- Blocks of bytes at base addresses. An earlier block hides later ones where they overlap.

The block `(base, bytes)` holds `bytes[i]` at address `base + i`. -/
abbrev Image := List (Nat × List Byte)

/-- The byte table an image denotes.

The blocks are installed from the last to the first, so the first block of the list is
installed last and its bytes win where blocks overlap. -/
def Image.bytes : Image → ByteMemory
  | [] => ∅
  | (base, block) :: rest => Memory.install (Image.bytes rest) base block

/-- The byte an image holds at an address, by list lookup.

It is the byte of the first block that covers the address: block `(base, block)` covers
`address` when `block[address - base]` exists and `base ≤ address`. If no block covers the
address, the result is `none`. -/
def Image.get? : Image → Nat → Option Byte
  | [], _ => none
  | (base, block) :: rest, address =>
    if base ≤ address then (block[address - base]?).or (Image.get? rest address)
    else Image.get? rest address

/-- `n` bytes starting at `address`, by list lookup; `none` if any is missing.

The bytes come in address order: the byte at `address` first. There is no permission check
here; `Image.checkedRead` adds it. -/
def Image.read (image : Image) (address : Nat) : Nat → Option (List Byte)
  | 0 => some []
  | n + 1 => do
    let byte ← image.get? address
    let tail ← Image.read image (address + 1) n
    pure (byte :: tail)

/-- The memory with the given regions whose bytes are the image's.

The regions are taken as given and are not compared with the image. -/
def Image.memory (regions : List Region) (image : Image) : Memory :=
  { regions := regions, bytes := image.bytes }

/-! ## The accesses in list form -/

/-- What `readLE` gives on `Image.memory regions image`, by list lookup
(`Image.readLE_memory`).

The permission check is the one of the memory: every byte of the span must lie below `2^64`
and in a region that allows `access`. That check looks only at the regions. Then the `n`
bytes are read from the image and put together least significant first. -/
def Image.checkedRead (regions : List Region) (image : Image) (access : Access)
    (address : BitVec 64) (n : Nat) : Option (BitVec (8 * n)) :=
  if (Image.memory regions image).checkSpan access address.toNat n then
    (image.read address.toNat n).map (ofBytesLE n)
  else none

/-- The image after `store` on `Image.memory regions image` (`Image.store_memory`).

If every byte of the span may be written, the bytes of `value`, least significant first,
become a new first block; the old blocks stay and are hidden where the new block covers
them. Otherwise the result is `none`. -/
def Image.checkedStore (regions : List Region) (image : Image) (address : BitVec 64) (n : Nat)
    (value : BitVec (8 * n)) : Option Image :=
  if (Image.memory regions image).checkSpan .write address.toNat n then
    some ((address.toNat, bytesLE n value) :: image)
  else none

end Silmaril.Machine.AArch64
