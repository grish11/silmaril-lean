module
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.DarkhttpdLogEncoding
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Darkhttpd.N117.Default.X8664.O0.Unstripped.DarkhttpdBinary
theorem code_at : Silmaril.Elf.CodeAt F address code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
theorem symbol_identity :
    s28_90.name = ("needs_logencoding".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_90.raw.value = address ∧ s28_90.raw.size = 41 ∧ s28_90.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.DarkhttpdLogEncoding
