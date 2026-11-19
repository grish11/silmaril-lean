module
public import Silmaril.Elf.Corpus.CjsonArraySize.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonArraySize
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1
theorem code_at : Silmaril.Elf.CodeAt F address code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem symbol_identity :
    s3_42.name = ("cJSON_GetArraySize".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_42.raw.value = address ∧ s3_42.raw.size = 35 ∧ s3_42.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.CjsonArraySize
