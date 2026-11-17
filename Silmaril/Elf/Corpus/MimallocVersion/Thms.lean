module

public import Silmaril.Elf.Corpus.MimallocVersion.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Unstripped.LibmimallocSo21.Functions
public import Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Unstripped.LibmimallocSo21.Functions

/-! Kernel binding of the problem's actual instruction bytes to delivered ELF files.
These byte-location theorems do not prove `Task.mi_version_equivalent`. -/

@[expose] public section

namespace Silmaril.Elf.Corpus.MimallocVersion

open Silmaril.Elf.Staged.Reader

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Unstripped.LibmimallocSo21 in
/-- The O0 function's bytes are at its ELF virtual address. -/
theorem codeO0_at : Silmaril.Elf.CodeAt O0 0x11e2f codeO0 :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Unstripped.LibmimallocSo21 in
/-- The O3 function's bytes are at its ELF virtual address. -/
theorem codeO3_at : Silmaril.Elf.CodeAt O3 0xfaf0 codeO3 :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Unstripped.LibmimallocSo21 in
/-- The parsed exported symbol has the exact name, address and length used by the problem. -/
theorem symbolO0_identity :
    s3_204.name = ("mi_version".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_204.raw.value = 0x11e2f ∧ s3_204.raw.size = 11 ∧ s3_204.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Unstripped.LibmimallocSo21 in
/-- The parsed exported symbol has the exact name, address and length used by the problem. -/
theorem symbolO3_identity :
    s3_205.name = ("mi_version".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_205.raw.value = 0xfaf0 ∧ s3_205.raw.size = 6 ∧ s3_205.kind = 2 := by
  decide +kernel

end Silmaril.Elf.Corpus.MimallocVersion
