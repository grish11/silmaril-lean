module
public import Silmaril.Elf.Corpus.CjsonArrayItem.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArrayItem
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1
theorem code_at : Silmaril.Elf.CodeAt F address code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem symbol_identity :
    s25_38.name = ("get_array_item".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s25_38.raw.value = address ∧ s25_38.raw.size = helperSize ∧ s25_38.kind = 2 ∧
    s25_116.name = ("cJSON_GetArrayItem".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s25_116.raw.value = callerAddress ∧ s25_116.raw.size = callerSize ∧ s25_116.kind = 2 ∧
    address+entryOffset = callerAddress := by decide +kernel
end Silmaril.Elf.Corpus.CjsonArrayItem
