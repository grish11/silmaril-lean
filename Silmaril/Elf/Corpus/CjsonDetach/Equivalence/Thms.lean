module
public import Silmaril.Elf.Corpus.CjsonDetach.Equivalence.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonDetach.Equivalence
open Silmaril.Elf.Staged.Reader
theorem actual_left_code : Silmaril.Elf.CodeAt
    Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.F 23724 leftCode :=
  Silmaril.Elf.Corpus.CjsonDetach.code_at
open Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1 in
theorem actual_right_code : Silmaril.Elf.CodeAt F 17248 rightCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1 in
theorem actual_right_symbol :
    s25_121.name = ("cJSON_DetachItemViaPointer".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s25_121.raw.value = 17248 ∧ s25_121.raw.size = 131 ∧ s25_121.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.CjsonDetach.Equivalence
