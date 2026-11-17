module

public import Silmaril.Elf.Abi.Defs
public import Silmaril.Elf.Asm.Defs

/-!
# ABI conformance over assembly functions: the typed adapter

An assembly function (`Silmaril.Elf.Asm.AsmFunction`: name, extent, exact bytes, symbol, listing,
references) is the code a conformance row is about. `Code.ofAsm f image` is the conformance
`Machine.Abi.Conformance.Code` of `f`: its bytes at its virtual address, entered at offset 0,
the function's extent its size, the image ranges given (a row checks them against the file:
`CodeOf`).

The adapter reads only the function's typed fields, never its listing text or its `abiRef`: the
ABI a row is judged against is a typed `AbiDef`, and `abiRef` stays metadata. `Thms.codeOf_ofAsm`
turns the function's evidence (`BytesAt` in the first executable segment, `SymbolOf` an
`STT_FUNC`) and the binding's lookup into the row's `CodeOf`. A function that tail-calls another
(`adler32` → `adler32_z`) needs a region spanning both: a `Code` with an entry offset, not this
single-function form.
-/

@[expose] public section

namespace Silmaril.Elf.Abi

open Silmaril.Machine.Abi.Conformance
open Silmaril.Elf.Asm (AsmFunction)

/-- **The conformance code of an assembly function**: its bytes at its virtual address, entered
at offset 0, its extent's size, no read-only data, and the image ranges `image`. -/
def Code.ofAsm (f : AsmFunction) (image : List (Silmaril.X86.Word × Nat)) : Code where
  base := BitVec.ofNat 64 f.extent.vaddr
  bytes := f.bytes
  off := 0
  len := f.extent.size
  image := image

end Silmaril.Elf.Abi

end
