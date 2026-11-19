module
public import Silmaril.Elf.Corpus.CjsonSuffix.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonSuffix
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1
theorem code_at : Silmaril.Elf.CodeAt F address code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem symbol_identity :
    s25_40.name = ("suffix_object".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s25_40.raw.value = address ∧ s25_40.raw.size = 38 ∧ s25_40.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.CjsonSuffix
