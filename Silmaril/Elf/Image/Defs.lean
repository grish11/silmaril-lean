module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Elf.Staged.Defs

/-! # File offsets, virtual addresses, load addresses and zero fill (`Silmaril.Elf.Image`)

Four address spaces meet in an ELF file, and a statement must say which one it is about:

| space | what it indexes | where it comes from |
|---|---|---|
| file offset | the bytes of the file (`blobRead F o w`) | `p_offset`, `sh_offset` |
| virtual address | the link-time image (`p_vaddr`, `st_value`, `e_entry`) | the file's metadata |
| load address | memory after loading at a base | `base + v` for `ET_DYN`, `v` for `ET_EXEC` (`Placement`) |
| zero fill | addresses in `[p_vaddr + p_filesz, p_vaddr + p_memsz)` (`.bss`) | no file byte at all |

* `segOrigin ph v`: where the byte at virtual address `v` comes from in one segment: a file
  offset (`Origin.file o`), zero fill (`Origin.zeroFill`), or nothing (`none`, not mapped by it).
* `File.origins A v`: **every** `PT_LOAD` that maps `v`, by program-header index. The parse does not
  reject overlapping segments, so this is a list: `[]` (unmapped), one entry, or several
  (`File.resolve`: `unmapped | unique | ambiguous`). Nothing here picks one silently; the first-match
  conventions of `CodeAt` (`List.find?`) and of `Staged.Layout.offsetOf` are related to it by
  theorems (`Thms`), and agree with it exactly when the mapping is unique.
* `MapsFile A i v len o`: program header `i` is a `PT_LOAD` that maps the `len` bytes at `v` from
  the file bytes at offset `o` (all of them file-backed: none zero fill).
* `FileBytes F o bytes`: the file holds `bytes` at offset `o` — a statement about the file, not
  about memory.
* `SegBytes F A i v o bytes`: both: segment `i` of the parse `A` maps `bytes`, which the file holds
  at `o`, to `v`.
* `Untouched A v len`: no dynamic relocation writes into `[v, v + len)` (conservatively, each
  writes at most 8 bytes, the widest x86-64 dynamic relocation). Without it, memory after loading
  need not hold the file bytes: the loader patches relocated words. Statements about loaded
  memory take it (or a loading model, `Silmaril.Elf.Link.ElfBind`) as a hypothesis.

Not modelled: page granularity (the loader maps whole pages, so bytes outside `[p_offset,
p_offset + p_filesz)` on the same page are visible in memory; nothing here claims anything about
them), `p_filesz > p_memsz` (treated as mapping the file bytes; `Placement` excludes it), and
permissions beyond the read/execute bits `CodeAt` already checks.
-/

@[expose] public section

namespace Silmaril.Elf.Image

open Silmaril.Formats.ELF (ProgramHeader)
open Silmaril.Elf.Link.DynElf (blobRead)
open Silmaril.X86.Link (Blob)

/-- Where a byte of a loaded segment comes from. -/
inductive Origin where
  /-- The file byte at this offset. -/
  | file (off : Nat)
  /-- Zero fill: past `p_filesz`, before `p_memsz`. No file byte. -/
  | zeroFill
  deriving DecidableEq, Repr

/-- **Where the byte at virtual address `v` comes from in segment `ph`**, if `ph` maps it. -/
def segOrigin (ph : ProgramHeader) (v : Nat) : Option Origin :=
  if ph.kind = PT_LOAD ∧ ph.virtualAddress ≤ v then
    if v < ph.virtualAddress + ph.fileSize then some (.file (ph.offset + (v - ph.virtualAddress)))
    else if v < ph.virtualAddress + ph.memorySize then some .zeroFill
    else none
  else none

/-- **Every segment that maps `v`**, by program-header index, with the origin each gives. -/
def _root_.Silmaril.Elf.File.origins (A : File) (v : Nat) : List (Nat × Origin) :=
  A.phdrs.zipIdx.filterMap fun (ph, i) => (segOrigin ph v).map ((i, ·))

/-- How a virtual address resolves. -/
inductive Resolution where
  /-- No `PT_LOAD` maps it. -/
  | unmapped
  /-- Exactly one does: program header `i`, with origin `o`. -/
  | unique (i : Nat) (o : Origin)
  /-- Several do (overlapping segments): every one of them, in program-header order. -/
  | ambiguous (hits : List (Nat × Origin))
  deriving DecidableEq, Repr

/-- **How `v` resolves in `A`.** -/
def _root_.Silmaril.Elf.File.resolve (A : File) (v : Nat) : Resolution :=
  match A.origins v with
  | [] => .unmapped
  | [(i, o)] => .unique i o
  | hs => .ambiguous hs

/-- **Program header `i` maps the `len` bytes at virtual address `v` from file offset `o`**,
every one of them file-backed. -/
def MapsFile (A : File) (i v len o : Nat) : Prop :=
  ∃ ph, A.phdrs[i]? = some ph ∧ ph.kind = PT_LOAD ∧ ph.virtualAddress ≤ v ∧
    v + len ≤ ph.virtualAddress + ph.fileSize ∧ o = ph.offset + (v - ph.virtualAddress)

/-- **The file holds `bytes` at offset `o`** (a fact about the file, not about memory). -/
def FileBytes (F : Blob) (o : Nat) (bytes : List (BitVec 8)) : Prop :=
  blobRead F o bytes.length = some (Blob.valueLE bytes)

/-- **Segment `i` of `A` maps `bytes`, which `F` holds at offset `o`, to virtual address `v`.** -/
def SegBytes (F : Blob) (A : File) (i v o : Nat) (bytes : List (BitVec 8)) : Prop :=
  MapsFile A i v bytes.length o ∧ FileBytes F o bytes

/-- **Every byte of `[v, v + len)` resolves uniquely.** -/
def Unambiguous (A : File) (v len : Nat) : Prop :=
  ∀ k, k < len → (A.origins (v + k)).length = 1

instance (A : File) (v len : Nat) : Decidable (Unambiguous A v len) :=
  inferInstanceAs (Decidable (∀ k, k < len → _))

/-- **No dynamic relocation writes into `[v, v + len)`** (each assumed to write at most 8 bytes). -/
def Untouched (A : File) (v len : Nat) : Prop :=
  ∀ r ∈ A.relocs .dynamic, r.offset + 8 ≤ v ∨ v + len ≤ r.offset

instance (A : File) (v len : Nat) : Decidable (Untouched A v len) :=
  inferInstanceAs (Decidable (∀ r ∈ A.relocs .dynamic, _))

/-- The load address of virtual address `v` at base `base` (`Placement F base` says which bases a
statement covers: `0` for `ET_EXEC`). -/
def loadAddr (base v : Nat) : Nat := base + v

end Silmaril.Elf.Image
