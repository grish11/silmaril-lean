module

public import Silmaril.Machine.AArch64.Memory.Image.Defs
public import Silmaril.Machine.AArch64.Memory.Thms
import Silmaril.Proofs.Machine.AArch64.Memory.Image

/-!
# AArch64 memory images: the bridge to lists, and how to check a concrete example

Statements about `Silmaril.Machine.AArch64.Memory.Image.Defs`. That module says why images
exist: the kernel cannot evaluate the hash map of the reused memory, and it can evaluate
lists. Worked examples are in `Silmaril.Machine.AArch64.Memory.Examples.Thms`.

## The statements

* **What the definitions are.** `Image.memory_regions`, `Image.memory_bytes`: the memory of
  an image has the given regions and the bytes of the image. `Image.bytes_nil`: the empty
  image holds no byte. `Image.bytes_cons`: a block in front of an image is installed over
  the bytes of the image.
* **Bridge.** `Image.bytes_get?`: the hash map of an image and the list lookup give the
  same byte. `Image.readBacking_bytes`: the same for `n` bytes. `Image.readWith_memory`: a
  checked read of `Image.memory regions image` is the permission check and then a list
  lookup. `Image.readBytes_memory`, `Image.fetchBytes_memory`: its cases for read and for
  execute permission. `Image.writeBytes_memory`: a checked write puts the written block in
  front of the image.
* **Permission check.** `Image.checkSpan_memory`: the check looks only at the regions.
* **Accesses in list form.** `Image.readLE_memory`, `Image.fetchWord_memory`,
  `Image.load_memory`, `Image.loadByte_memory`: a read of `Image.memory regions image` is
  `Image.checkedRead`. `Image.store_memory`: a store gives the memory of
  `Image.checkedStore`.
* **After a store or a write.** `Image.bind_map_memory`, `Image.do_map_memory`,
  `Image.map_map_memory`: what follows a store is given the new image, so its accesses can
  be put in list form too. `Image.ite_some_memory`: the result of a checked write of the
  reused memory has the same form as the result of a store.
* **The simp set `aarch64_image`.** Its members are the thirteen equations for accesses:
  the four of the bridge for `readWith`, `readBytes`, `fetchBytes` and `writeBytes`, and the
  nine of the last two items. It is registered in
  `Silmaril.Machine.AArch64.Memory.Image.Defs`.
* **A store with its image written out.** `Image.store_memory_eq_some`,
  `Image.store_memory_eq_some_iff`.

## The recipe

To prove a concrete fact about fetches, loads and stores on `Image.memory regions image`,
or about the checked reads and writes of the reused memory on it:

```
  simp only [aarch64_image]
  decide
```

The first line rewrites every access into its list form, with the equations of the simp set
`aarch64_image`. The second line lets the kernel evaluate the lists. Both lines are checked
by the kernel; nothing is evaluated by compiled code. For a single access, `rw` with its one
equation does the same as the first line, for example `rw [Image.fetchWord_memory]`.

The first line is the same for every example: it does not matter which of the equations an
example needs. A later layer that has equations of its own for image-backed memories can
tag them `@[aarch64_image]`, or pass them next to the set:
`simp only [aarch64_image, other]`.

The recipe proves, on the example memory of
`Silmaril.Machine.AArch64.Memory.Examples.Defs` (the theorems are in
`Silmaril.Machine.AArch64.Memory.Examples.Thms`):

* one fetch: `fetchWord memory 0x1000#64 = some 0x44332211#32`;
* one load of 1, 4 or 8 bytes: `load memory 0x2000#64 8 = some 0x8877665544332211#64`;
* a store followed by a load:
  `(store memory 0x4004#64 4 0xAABBCCDD#32).bind (fun m => load m 0x4004#64 4) = some …`;
* two stores followed by a load and a fetch (`two_stores_then_load_and_fetch` there);
* a disequality: `fetchWord memory 0x1000#64 ≠ some 0x11223344#32`;
* failures: `fetchWord memory 0x2000#64 = none`, `store memory 0x2000#64 4 v = none`;
* the reused memory's own functions: `memory.readBytes 0x2000 4 = some […]`, and a
  `writeBytes` followed by a `readBytes`;
* conjunctions of such facts.

## How to state an example so that the recipe applies

* **The memory must be visibly an image.** Write `Image.memory regions image`, or give it a
  name with `abbrev`. If the name is a `def`, the first line finds nothing to rewrite and
  says that `simp` made no progress; then add the name: `simp only [name, aarch64_image]`.
* **What follows a store.** State it with `Option.bind`, with `Option.map`, or in `do`
  notation, as in the examples. Then the memory after the store is a bound variable, and
  the first line of the recipe replaces it by the image after the store. A `match` on the
  result of a store is not rewritten. The same holds for what follows a `writeBytes`.
* **A store with its image written out.** To state that a store gives the memory of a
  given image, use `exact Image.store_memory_eq_some (by decide)`; this is `store_image`
  in the examples. There is no decision procedure for equality of two memories, so the
  recipe does not apply to such a statement.
* **A store as a hypothesis.** From `stored : store (Image.memory regions image) … = some after`,
  `obtain ⟨-, rfl⟩ := Image.store_memory_eq_some_iff.mp stored` replaces `after` by an
  image-backed memory; this is `load_of_store` in the examples.

## Limits

* **Long blocks.** `decide` first evaluates in the elaborator, which stops with
  "maximum recursion depth has been reached" when a lookup has to walk more than about 400
  bytes into one block (measured: 440 bytes work, 480 do not). `decide +kernel` leaves the
  evaluation to the kernel alone and has no such limit. The kernel checks the proof either
  way, so `decide +kernel` is the second line to use for larger images. The kernel still
  walks the lists: reading four bytes at offset 2000 of a block takes about a quarter of a
  second.
* **Many stores.** Each store adds a block, and a lookup walks the blocks in order. A chain
  of 64 stores and a load is still checked in well under a second.
* **An access left in hash-map form.** On a small image, if `decide` stops with "maximum
  recursion depth has been reached", or `decide +kernel` says that it "failed to reduce" or
  reports a kernel "application type mismatch" about `Eq.refl true`, then some access was
  not rewritten: see "How to state an example" above. A wrong expected value gives a
  different message: `decide` "proved that the proposition … is false".

Proofs longer than a few lines: module `Silmaril.Proofs.Machine.AArch64.Memory.Image`.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64

open Silmaril.Process (Memory Byte Access Region)

/-! ## What the definitions are

These four hold by definition. They are stated so that the definitions are fixed by
statements too: the bridge alone would also hold for a memory that dropped its regions. -/

/-- The memory of an image has exactly the given regions. -/
theorem Image.memory_regions (regions : List Region) (image : Image) :
    (Image.memory regions image).regions = regions :=
  rfl

/-- The memory of an image has exactly the bytes of the image. -/
theorem Image.memory_bytes (regions : List Region) (image : Image) :
    (Image.memory regions image).bytes = image.bytes :=
  rfl

/-- The empty image holds no byte. -/
theorem Image.bytes_nil : Image.bytes [] = ∅ :=
  rfl

/-- A block in front of an image is installed over the bytes of the image: it gives the
bytes it covers, and the image gives the others. -/
theorem Image.bytes_cons (base : Nat) (block : List Byte) (image : Image) :
    Image.bytes ((base, block) :: image) = Memory.install image.bytes base block :=
  rfl

/-! ## The bridge between the hash map and the lists

`Image.readWith_memory`, `Image.readBytes_memory`, `Image.fetchBytes_memory` and
`Image.writeBytes_memory` are members of the simp set `aarch64_image`, so the recipe also
rewrites a statement that uses the reused memory's own functions. -/

/-- **Bridge, one byte.** The hash map an image denotes and the list lookup give the same
byte at every address: the same value, or `none` in both. -/
theorem Image.bytes_get? (image : Image) (address : Nat) :
    image.bytes.get? address = image.get? address :=
  Silmaril.Proofs.Machine.AArch64.Memory.Image.bytes_get? image address

/-- **Bridge, `n` bytes.** Reading `n` bytes of the hash map of an image is reading them by
list lookup. No permission is checked on either side. -/
theorem Image.readBacking_bytes (image : Image) (address n : Nat) :
    Memory.readBacking image.bytes address n = image.read address n :=
  Silmaril.Proofs.Machine.AArch64.Memory.Image.readBacking_bytes image address n

/-- **Bridge, checked read.** A checked read of an image-backed memory is the permission
check followed by a list lookup. -/
@[aarch64_image]
theorem Image.readWith_memory (regions : List Region) (image : Image) (access : Access)
    (address n : Nat) :
    (Image.memory regions image).readWith access address n =
      if (Image.memory regions image).checkSpan access address n then image.read address n
      else none := by
  rw [Memory.readWith, ← Image.readBacking_bytes]
  rfl

/-- **Bridge, checked write.** A permitted write of `block` at `address` gives the memory of
the image with `(address, block)` in front. The new block hides the old bytes it covers, and
the regions are the same. A write that is not permitted gives `none`. -/
@[aarch64_image]
theorem Image.writeBytes_memory (regions : List Region) (image : Image) (address : Nat)
    (block : List Byte) :
    (Image.memory regions image).writeBytes address block =
      if (Image.memory regions image).checkSpan .write address block.length then
        some (Image.memory regions ((address, block) :: image)) else none :=
  rfl

/-- The bridge for `Memory.readBytes`: a checked read with read permission. -/
@[aarch64_image]
theorem Image.readBytes_memory (regions : List Region) (image : Image) (address n : Nat) :
    (Image.memory regions image).readBytes address n =
      if (Image.memory regions image).checkSpan .read address n then image.read address n
      else none :=
  Image.readWith_memory regions image .read address n

/-- The bridge for `Memory.fetchBytes`: a checked read with execute permission. -/
@[aarch64_image]
theorem Image.fetchBytes_memory (regions : List Region) (image : Image) (address n : Nat) :
    (Image.memory regions image).fetchBytes address n =
      if (Image.memory regions image).checkSpan .execute address n then image.read address n
      else none :=
  Image.readWith_memory regions image .execute address n

/-! ## The permission check -/

/-- **The permission check looks only at the regions.** Two image-backed memories with the
same regions allow the same accesses, whatever their images hold. In particular the check
is unchanged by a store, and it can be evaluated without any byte lookup. -/
theorem Image.checkSpan_memory (regions : List Region) (image other : Image) (access : Access)
    (address n : Nat) :
    (Image.memory regions image).checkSpan access address n =
      (Image.memory regions other).checkSpan access address n :=
  rfl

/-! ## The accesses in list form

The equations of this section and of the next are members of the simp set `aarch64_image`,
as are the four equations of the bridge for `readWith`, `readBytes`, `fetchBytes` and
`writeBytes`. -/

/-- A checked little-endian read of an image-backed memory, in list form. -/
@[aarch64_image]
theorem Image.readLE_memory (regions : List Region) (image : Image) (access : Access)
    (address : BitVec 64) (n : Nat) :
    readLE (Image.memory regions image) access address n =
      Image.checkedRead regions image access address n := by
  rw [readLE, Image.readWith_memory, Image.checkedRead]
  split <;> rfl

/-- A fetch from an image-backed memory, in list form: four bytes with execute permission. -/
@[aarch64_image]
theorem Image.fetchWord_memory (regions : List Region) (image : Image) (address : BitVec 64) :
    fetchWord (Image.memory regions image) address =
      Image.checkedRead regions image .execute address 4 :=
  Image.readLE_memory regions image .execute address 4

/-- A load from an image-backed memory, in list form: `n` bytes with read permission. -/
@[aarch64_image]
theorem Image.load_memory (regions : List Region) (image : Image) (address : BitVec 64)
    (n : Nat) :
    load (Image.memory regions image) address n =
      Image.checkedRead regions image .read address n :=
  Image.readLE_memory regions image .read address n

/-- A one-byte load from an image-backed memory, in list form. -/
@[aarch64_image]
theorem Image.loadByte_memory (regions : List Region) (image : Image) (address : BitVec 64) :
    loadByte (Image.memory regions image) address =
      Image.checkedRead regions image .read address 1 :=
  Image.readLE_memory regions image .read address 1

/-- A store to an image-backed memory, in list form. If the store is permitted, the memory
after it is the memory of the image with the stored bytes in front; so it is again
image-backed, with the same regions. If not, both sides are `none`. -/
@[aarch64_image]
theorem Image.store_memory (regions : List Region) (image : Image) (address : BitVec 64)
    (n : Nat) (value : BitVec (8 * n)) :
    store (Image.memory regions image) address n value =
      (Image.checkedStore regions image address n value).map (Image.memory regions) := by
  rw [store, Image.writeBytes_memory, Image.checkedStore, bytesLE_length]
  split <;> rfl

/-! ## What follows a store

After `Image.store_memory`, the result of a store is `stored.map (Image.memory regions)` for
an optional image `stored`. The next three statements hand the image, not the memory, to
whatever uses that result. Its accesses are then on `Image.memory regions image` for a bound
variable `image`, and the equations above apply to them. -/

/-- `Option.bind` after a store continues with the image. -/
@[aarch64_image]
theorem Image.bind_map_memory.{u} {α : Type u} (regions : List Region) (stored : Option Image)
    (next : Memory → Option α) :
    (stored.map (Image.memory regions)).bind next =
      stored.bind fun image => next (Image.memory regions image) := by
  cases stored <;> rfl

/-- `>>=` after a store continues with the image. This is the form that `do` notation
produces. Here `α` is in `Type`, because `>>=` needs both results in the universe of
`Memory`. -/
@[aarch64_image]
theorem Image.do_map_memory {α : Type} (regions : List Region) (stored : Option Image)
    (next : Memory → Option α) :
    (stored.map (Image.memory regions) >>= next) =
      stored >>= fun image => next (Image.memory regions image) :=
  Image.bind_map_memory regions stored next

/-- `Option.map` after a store continues with the image. -/
@[aarch64_image]
theorem Image.map_map_memory.{u} {α : Type u} (regions : List Region) (stored : Option Image)
    (next : Memory → α) :
    (stored.map (Image.memory regions)).map next =
      stored.map fun image => next (Image.memory regions image) := by
  cases stored <;> rfl

/-- The result of `Image.writeBytes_memory`, an image-backed memory or `none`, in the form
`stored.map (Image.memory regions)` of a store. So what follows a checked write of the
reused memory is given the image as well, by the three statements above. -/
@[aarch64_image]
theorem Image.ite_some_memory (regions : List Region) (image : Image) (permitted : Prop)
    [Decidable permitted] :
    (if permitted then some (Image.memory regions image) else none) =
      (if permitted then some image else none).map (Image.memory regions) := by
  split <;> rfl

/-! ## A store with its image written out -/

/-- If the list form of a store gives the image `after`, the store gives the memory of
`after`. The hypothesis is about lists only, so `by decide` proves it. -/
theorem Image.store_memory_eq_some {regions : List Region} {image after : Image}
    {address : BitVec 64} {n : Nat} {value : BitVec (8 * n)}
    (stored : Image.checkedStore regions image address n value = some after) :
    store (Image.memory regions image) address n value = some (Image.memory regions after) := by
  rw [Image.store_memory, stored, Option.map_some]

/-- A store to an image-backed memory succeeds exactly when the bytes may be written, and
then the memory after it is the memory of the image with the stored bytes in front. This is
`store_eq_some_iff` with the memory after the store in image form. -/
theorem Image.store_memory_eq_some_iff {regions : List Region} {image : Image}
    {address : BitVec 64} {n : Nat} {value : BitVec (8 * n)} {after : Memory} :
    store (Image.memory regions image) address n value = some after ↔
      (Image.memory regions image).Permitted .write address.toNat n ∧
        after = Image.memory regions ((address.toNat, bytesLE n value) :: image) :=
  store_eq_some_iff

end Silmaril.Machine.AArch64
