module

public import Silmaril.X86.Basic

-- AMD64 psABI relocation table:
-- https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/e1ce098331da5dbd66e1ffc74162380bcc213236/x86-64-ABI/object-files.tex#L440
/-!
The AMD64 psABI specifies `R_X86_64_64` as `S + A` in a `word64` field. The
[ELF generic ABI](https://gabi.xinuos.com/elf/06-reloc.html) gives `Elf64_Rela`
a signed `Elf64_Sxword` addend. [glibc 2.41](https://github.com/bminor/glibc/blob/glibc-2.41/sysdeps/x86_64/dl-machine.h#L415)
writes the sum using unsigned 64-bit arithmetic.

The input `resolved` is the already resolved symbol word. Symbol lookup,
slot placement, and loading are outside this computation.
-/

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationValue

open Silmaril.X86 (Word)

/-- The resolved symbol value plus the signed RELA addend, modulo 2^64. -/
def abs64 (resolved : Word) (addend : Int) : Word :=
  resolved + BitVec.ofInt 64 addend

end Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationValue
