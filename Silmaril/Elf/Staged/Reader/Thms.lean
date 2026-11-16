module

public import Silmaril.Elf.Staged.Reader.Defs
public import Silmaril.Elf.Staged.Thms
public import Silmaril.Elf.Facts.Defs
import Silmaril.Proofs.Elf.Staged.Reader

/-! # The kernel-bytes reader is sound

* `sub_kbytes`: kernel bytes with the raw file's bytes answer as that file (`Check.Sub`).
* `sub_window`: restricting a source to windows keeps it sound.
* `partIs_of_kbytes`, `zerosAt_of_kbytes`: a part (or zero padding) of the raw file from one
  kernel run on its kernel bytes.
* `codeAt_of_kbytes`: `Silmaril.Elf.CodeAt` of the raw file from one kernel read.
* `PartIs.run`, `PartIs.layoutIs`, `PartIs.bodyIs`, `PartIs.loaderIs`: a part as a fact of the
  specification and of the staged parse.

Proofs: `Silmaril.Proofs.Elf.Staged.Reader` (standard axioms only).
-/

@[expose] public section

namespace Silmaril.Elf.Staged.Reader

open Silmaril.Formats.ELF (SectionHeader)
open Silmaril.Elf.Link.DynElf (Rd blobRead)
open Silmaril.Elf.Check (Src Sub)
open Silmaril.X86.Link (Blob)

/-- **Kernel bytes answer as the file of their bytes.** -/
theorem sub_kbytes {x : KBytes} (hx : x.wf = true) {raw : ByteArray} (h : x.toByteArray = raw) :
    Sub (kread x) (blobOf ⟨raw⟩) :=
  Proofs.Elf.Staged.Reader.sub_kbytes hx h

/-- A source restricted to windows answers as the file when the source does. -/
theorem sub_window {r : Src} {F : Blob} (hs : Sub r F) (ws : List Span) : Sub (window ws r) F :=
  Proofs.Elf.Staged.Reader.sub_window hs ws

/-- **A part of the raw file from a kernel run on its kernel bytes.** -/
theorem partIs_of_kbytes {α : Type} {x : KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) {ws : List Span} {p : Rd α} {v : α}
    (hc : p.run (window ws (kread x)) = some v) : PartIs (blobOf ⟨raw⟩) ws p v :=
  Proofs.Elf.Staged.Reader.partIs_of_sub (sub_kbytes hx h) hc

/-- **Zero bytes of the raw file from a kernel read of its kernel bytes.** -/
theorem zerosAt_of_kbytes {x : KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) {o n : Nat} (hc : kread x o n = some 0) :
    ZerosAt (blobOf ⟨raw⟩) o n :=
  sub_kbytes hx h o n 0 hc

/-- **Code at a virtual address of the raw file** (`Silmaril.Elf.CodeAt`), from its parse, the
`PT_LOAD` that maps the address, and one kernel read of the code's bytes on kernel bytes. -/
theorem codeAt_of_kbytes {x : KBytes} (hx : x.wf = true) {raw : ByteArray}
    (h : x.toByteArray = raw) {A : File} (hp : Parses (blobOf ⟨raw⟩) A) {v : Nat}
    {code : List (BitVec 8)} {ph : Silmaril.Formats.ELF.ProgramHeader}
    (hf : A.phdrs.find? (codeSeg v code.length) = some ph)
    (hc : kread x (ph.offset + (v - ph.virtualAddress)) code.length =
      some (Silmaril.X86.Link.Blob.valueLE code)) : CodeAt (blobOf ⟨raw⟩) v code :=
  ⟨A, hp, ph, hf, sub_kbytes hx h _ _ _ hc⟩

/-- A part is what the specification's reader returns on the whole file. -/
theorem PartIs.run {α : Type} {F : Blob} {ws : List Span} {p : Rd α} {v : α}
    (h : PartIs F ws p v) : p.run (blobRead F) = some v :=
  Rd.run_mono (sub_window (Proofs.Elf.Staged.Reader.sub_blobRead F) ws) _ _ h

theorem PartIs.layoutIs {F : Blob} {ws : List Span} {L : Layout} (h : PartIs F ws readLayout L) :
    LayoutIs F L :=
  h.run

theorem PartIs.bodyIs {F : Blob} {ws : List Span} {L : Layout} {sh : SectionHeader} {b : Body}
    (h : PartIs F ws (Parse.body L.shs sh) b) : BodyIs F L sh b :=
  h.run

theorem PartIs.loaderIs {F : Blob} {ws : List Span} {L : Layout} {ld : Loader}
    (h : PartIs F ws (readLoader L.phdrs) ld) : LoaderIs F L ld :=
  h.run

end Silmaril.Elf.Staged.Reader
