module
public import Silmaril.Elf.Corpus.CjsonArraySize.Equivalence.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1.Thms
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArraySize.Equivalence
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1 in
theorem actual_left_code : Silmaril.Elf.CodeAt F 21378 leftCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1 in
theorem actual_left_symbol :
    s25_95.name = ("cJSON_GetArraySize".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s25_95.raw.value = 21378 ∧ s25_95.raw.size = 81 ∧ s25_95.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.CjsonArraySize.Equivalence
