module
public import Silmaril.Elf.Corpus.CjsonDetach.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonDetach
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1
theorem code_at : Silmaril.Elf.CodeAt F address code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem symbol_identity :
    s25_149.name = ("cJSON_DetachItemViaPointer".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s25_149.raw.value = address ∧ s25_149.raw.size = 218 ∧ s25_149.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.CjsonDetach
