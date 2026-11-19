module
public import Silmaril.Elf.Corpus.MimallocOsGlobals.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsGlobals
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21
theorem page_at : Silmaril.Elf.CodeAt F Getter.page.address Getter.page.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem page_symbol : s28_179.name = (Getter.page.name.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_179.raw.value = Getter.page.address ∧ s28_179.raw.size = 8 ∧ s28_179.kind = 2 := by decide +kernel
theorem largePage_at : Silmaril.Elf.CodeAt F Getter.largePage.address Getter.largePage.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem largePage_symbol : s28_219.name = (Getter.largePage.name.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_219.raw.value = Getter.largePage.address ∧ s28_219.raw.size = 19 ∧ s28_219.kind = 2 := by decide +kernel
theorem global_symbol : s28_126.name = ("mi_os_mem_config".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_126.raw.value = globalAddress ∧ s28_126.raw.size = 48 ∧ s28_126.kind = 1 := by decide +kernel
end Silmaril.Elf.Corpus.MimallocOsGlobals
