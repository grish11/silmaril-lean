module

public import Silmaril.Elf.Facts.Defs
public import Silmaril.Project.Shapes.Abi.Defs

/-!
# Standard problem shapes: ABI conformance of a function of an ELF file

`silmaril.shapes.elf.abi_conforms` is `silmaril.shapes.abi.conforms` with the code **bound to
the file**: the ELF symbol lookup `sel` (ld.so's versioned lookup in `.dynsym`, or `.symtab`)
names the header's function `f` and finds a plain function at the code's entry
(`st_value = base + off`) whose size is the code's extent (`st_size = len`); a read-only
executable `PT_LOAD` of the file maps the code bytes at `base`; the read-only data the code
reads are mapped by the file too. Nothing about the code is taken from a tool: every one of
these facts reads the file through the ELF specification (`Silmaril.Elf.Facts`).

An ELF symbol has a value and a size but **no C signature**: the prototype comes from the
header (`Conforms.declared`), and the symbol only locates the code. So a row of this shape is
three separate statements that the explorer shows separately: the symbol is present
(`Lookup`), the code is the file's (`CodeAt`, `MappedAt`), and the code conforms (`Conforms`).

`silmaril.shapes.elf.abi_header_sat` is header satisfaction for one file: the claimed
functions each have a row, an `absent` exclusion is checked against the file (the lookup finds
nothing: an API version gap), and the coverage is checked against the header.

A header shared by several binaries (zlib's `zlib.h` for a static build and for a distribution's
`libz.so.1`) gives one set of rows **per binary**: the header and the specs are the same
values, the files, selectors (versions) and code differ.
-/

@[expose] public section

namespace Silmaril.Elf.Abi

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.X86.Link (Blob)
open Silmaril.Elf.Link.DynElf (blobRead)

/-- The name a selector looks up. -/
def selName : Sel → Silmaril.Formats.ELF.NameBytes
  | .dyn r => r.name
  | .sym n => n
  | .fn r => r.name

/-- `ph` is a `PT_LOAD` mapping `[v, v + len)` from the file, readable and not writable. -/
def roSeg (v len : Nat) (ph : Silmaril.Formats.ELF.ProgramHeader) : Bool :=
  ph.kind == PT_LOAD && ph.flags / 2 % 2 == 0 && ph.flags / 4 % 2 == 1 &&
    decide (ph.virtualAddress ≤ v) && decide (v + len ≤ ph.virtualAddress + ph.fileSize)

/-- **`F` maps `bytes` read-only at `v`** (any read-only `PT_LOAD`, as `CodeAt` for code). -/
def MappedAt (F : Blob) (v : Nat) (bytes : List (BitVec 8)) : Prop :=
  ∃ A, Parses F A ∧ ∃ ph, A.phdrs.find? (roSeg v bytes.length) = some ph ∧
    blobRead F (ph.offset + (v - ph.virtualAddress)) bytes.length = some (Blob.valueLE bytes)

/-- **The code is the function `sel` of `F`**: the selector names `f`, its lookup finds a plain
function at the entry with the code's extent, the file maps the code bytes and the data. -/
def CodeOf (F : Blob) (sel : Sel) (f : String) (c : Code) : Prop :=
  selName sel = nameOf f ∧
  (∃ d, Lookup F sel (some d) ∧ d.value = c.base.toNat + c.off ∧ d.size = c.len ∧
    d.ifunc = false ∧ d.abs = false) ∧
  CodeAt F c.base.toNat c.bytes ∧
  ∀ d ∈ c.data, MappedAt F d.1.toNat d.2

/-- **The function `sel` of the ELF file `F` conforms to the ABI `A`** as the function `f` of the
header `hdr`: the code is the file's (`CodeOf`) and it conforms (`Conforms`). -/
@[problem "silmaril.shapes.elf.abi_conforms"
  (title := "A function of an ELF file conforms to a versioned ABI as its C header declares it")]
def AbiConforms (A : AbiDef) (M : Mach) (mode : Mode) (hdr : HeaderSrc) (f : String)
    (p : A.V.Proto) (F : Blob) (sel : Sel) (c : Code) (frame : Nat) (S : CallSpec A.V p) : Prop :=
  CodeOf F sel f c ∧ Conforms A M mode hdr f p c frame S

/-- **The ELF file `F` satisfies the claimed part of the header `hdr`**: the coverage is checked
against the header, every `absent` exclusion is absent from the file (`sel f` finds nothing),
and every claimed function is a conforming function of the file. -/
@[problem "silmaril.shapes.elf.abi_header_sat"
  (title := "An ELF file satisfies the claimed part of a C header under a versioned ABI")]
def AbiHeaderSat (A : AbiDef) (M : Mach) (hdr : HeaderSrc) (cov : Coverage) (F : Blob)
    (sel : String → Sel) (impl : String → Option (Impl A)) : Prop :=
  cov.check A hdr = true ∧
  (∀ f why, (f, Exclusion.absent why) ∈ cov.excluded → Lookup F (sel f) none) ∧
  ∀ f ∈ cov.claimed, ∃ i, impl f = some i ∧
    AbiConforms A M i.mode hdr f i.proto F (sel f) i.code i.frame i.spec

end Silmaril.Elf.Abi

end

silmaril instance silmaril.shapes.elf.abi_conforms.sysv_int_open
    (title := "abi_conforms, System V AMD64 INTEGER fragment, on the open machine (Open)") :=
  silmaril.shapes.elf.abi_conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
silmaril instance silmaril.shapes.elf.abi_conforms.sysv_int_open9
    (title := "abi_conforms, System V AMD64 INTEGER fragment, on the open machine (Open9)") :=
  silmaril.shapes.elf.abi_conforms (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open9.isa)
silmaril instance silmaril.shapes.elf.abi_header_sat.sysv_int_open
    (title := "abi_header_sat, System V AMD64 INTEGER fragment, on the open machine (Open)") :=
  silmaril.shapes.elf.abi_header_sat (A := Silmaril.Machine.Abi.Conformance.sysvInt)
    (M := Silmaril.X86.Open.isa)
