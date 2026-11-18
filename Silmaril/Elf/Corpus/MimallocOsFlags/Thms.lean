module
public import Silmaril.Elf.Corpus.MimallocOsFlags.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsFlags
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21
theorem overcommit_at : Silmaril.Elf.CodeAt F Getter.overcommit.address Getter.overcommit.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem overcommit_symbol : s28_160.name = (Getter.overcommit.name.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_160.raw.value = Getter.overcommit.address ∧ s28_160.raw.size = 8 ∧ s28_160.kind = 2 := by decide +kernel
theorem virtualReserve_at : Silmaril.Elf.CodeAt F Getter.virtualReserve.address Getter.virtualReserve.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem virtualReserve_symbol : s28_212.name = (Getter.virtualReserve.name.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_212.raw.value = Getter.virtualReserve.address ∧ s28_212.raw.size = 8 ∧ s28_212.kind = 2 := by decide +kernel
theorem global_symbol : s28_126.name = ("mi_os_mem_config".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_126.raw.value = globalAddress ∧ s28_126.raw.size = 48 ∧ s28_126.kind = 1 := by decide +kernel
end Silmaril.Elf.Corpus.MimallocOsFlags
