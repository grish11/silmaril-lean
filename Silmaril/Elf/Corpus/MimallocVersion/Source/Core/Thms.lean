module

public import Silmaril.Elf.Corpus.MimallocVersion.Source.Core.Defs
public import Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21.Functions
import Silmaril.Proofs.Elf.Corpus.MimallocVersion.SourceCore

@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocVersion.Source.Core

/-- Actual elaboration binds this source Ail to this Core procedure. -/
theorem elaborates : Task.elaborates :=
  Silmaril.Proofs.Elf.Corpus.MimallocVersion.SourceCore.elaborates

open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21 in
/-- Canonical ELF bytes at the actual exported function's virtual address. -/
theorem canonical_code_at : Silmaril.Elf.CodeAt F 0xe2b0 codeO3 :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21 in
/-- The parsed canonical exported function has the exact identity used by the placement. -/
theorem canonical_symbol_identity :
    s3_205.name = ("mi_version".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_205.raw.value = 0xe2b0 ∧ s3_205.raw.size = 6 ∧ s3_205.kind = 2 := by
  decide +kernel

end Silmaril.Elf.Corpus.MimallocVersion.Source.Core
