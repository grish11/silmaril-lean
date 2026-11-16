module

public import Silmaril.Elf.Staged.Defs
public import Silmaril.Prelude.Bytes.Defs

/-! # Reading an ELF file from kernel bytes, part by part (`Silmaril.Elf.Staged.Reader`)

The ELF specification (`Silmaril.Elf.read` and its sub-readers `Parse.header`, `Parse.phdr`,
`Parse.body`, …) is a reading program over a byte oracle. This module runs it on
**kernel bytes** (`Silmaril.KBytes`, the tree the kernel reads quickly) and states what one run
establishes about the **raw file** `F` it was built from:

* `kread x` is the byte oracle of `x` (`KBytes.readLE`); `Reader.sub_kbytes` (`Thms`): when
  `x.toByteArray = raw` (what `kbytes_def … of_include raw` proves without decoding a byte), every
  read `kread x` answers, the file `blobOf ⟨raw⟩` answers the same.
* `window ws r` answers only reads that lie inside one of the byte ranges `ws`.
* **`PartIs F ws p v`**: the specification's reader `p`, run on the bytes of `F` **inside `ws`
  only**, returns `v`. So `v` is determined by those bytes: the byte ranges a part claims are
  part of the theorem's statement, not of any metadata about it. `PartIs.run` forgets the
  windows (`p.run (blobRead F) = some v`), and `PartIs.bodyIs`/`loaderIs` give the stage facts
  of `Silmaril.Elf.Staged`, from which `Staged.parses_assemble` rebuilds `Parses F A`.
* **`ZerosAt F o n`**: the `n` bytes of `F` at `o` are zero (padding between parts).

Every fact is closed by `decide +kernel` on `kread x` of an `include_bytes` file
(`partIs_of_kbytes`, `zerosAt_of_kbytes`); no native evaluation is involved.
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Reader

open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Check (Src)
open Silmaril.X86.Link (Blob)

/-- The byte oracle of kernel bytes: the little-endian value of `w` bytes at `o`, if in range. -/
def kread (x : KBytes) : Src := x.readLE

/-- Some window holds the read of `w` bytes at `o`. -/
def inWindows (ws : List Span) (o w : Nat) : Bool := ws.any fun s => decide (s.Contains o w)

/-- **The reads of `r` restricted to the windows `ws`**: a read answers only if it lies inside
one window. -/
def window (ws : List Span) (r : Src) : Src := fun o w => if inWindows ws o w then r o w else none

/-- **The part of `F` that the reader `p` reads from the windows `ws` is `v`.** -/
def PartIs {α : Type} (F : Blob) (ws : List Span) (p : Rd α) (v : α) : Prop :=
  p.run (window ws (blobRead F)) = some v

/-- **The `n` bytes of `F` at offset `o` are zero.** -/
def ZerosAt (F : Blob) (o n : Nat) : Prop := blobRead F o n = some 0

end Silmaril.Elf.Staged.Reader
