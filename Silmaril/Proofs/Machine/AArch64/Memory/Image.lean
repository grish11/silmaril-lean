module

public import Silmaril.Machine.AArch64.Memory.Image.Defs

/-!
# AArch64 memory images: proofs

Proofs for `Silmaril.Machine.AArch64.Memory.Image.Thms`.

Method. `Image.bytes` installs the blocks with `Memory.install`, the first block of the list
last. So for the first block `(base, block)` and an address there are three cases, and they
are the three cases of `Image.get?`:

* `base ≤ address` and `address - base < block.length`: the block covers the address.
  `Memory.install_get` gives the byte `block[address - base]`.
* `base ≤ address` and `block.length ≤ address - base`: the address is past the block.
* `address < base`: the address is before the block.

In the last two cases `Memory.install_outside` says the block changes nothing at the
address, and the induction hypothesis answers for the rest of the image. This is
`bytes_get?`.

`readBacking_bytes` follows by induction on the number of bytes: `Memory.readBacking` and
`Image.read` have the same recursion, and `bytes_get?` relates the lookups.
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.AArch64.Memory.Image

open Silmaril.Machine.AArch64

/-- The hash map of an image and the list lookup give the same byte at every address. -/
theorem bytes_get? (image : Image) (address : Nat) :
    image.bytes.get? address = image.get? address := by
  induction image with
  | nil => simp [Image.bytes, Image.get?]
  | cons head rest ih =>
    obtain ⟨base, block⟩ := head
    rw [Image.bytes, Image.get?]
    by_cases from_base : base ≤ address
    · rw [ite_eq_left from_base]
      by_cases covered : address - base < block.length
      · have found := Silmaril.Process.Memory.install_get (Image.bytes rest) base block
          (address - base) covered
        rw [show base + (address - base) = address by omega] at found
        rw [found, List.getElem?_eq_getElem covered, Option.some_or]
      · rw [Silmaril.Process.Memory.install_outside _ _ _ _ (by omega), ih,
          List.getElem?_eq_none (by omega), Option.none_or]
    · rw [ite_eq_right from_base, Silmaril.Process.Memory.install_outside _ _ _ _ (by omega), ih]

/-- Reading the hash map of an image byte by byte is reading the image by list lookup. -/
theorem readBacking_bytes (image : Image) (address n : Nat) :
    Silmaril.Process.Memory.readBacking image.bytes address n = image.read address n := by
  induction n generalizing address with
  | zero => rfl
  | succ n ih => rw [Silmaril.Process.Memory.readBacking, Image.read, bytes_get?, ih]

end Silmaril.Proofs.Machine.AArch64.Memory.Image
