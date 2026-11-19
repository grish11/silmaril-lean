module
public import Silmaril.Elf.Corpus.TinyccClosed.Identifier.Variants.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.TinyccClosed.Identifier.Variants
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.Og.Unstripped.Tcc in
theorem codeOg_at : Silmaril.Elf.CodeAt F 0x5e05 codeOg :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.Og.Unstripped.Tcc in
theorem symbolOg_identity :
    s29_47.name = ("isid".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s29_47.raw.value = 0x5e05 ∧ s29_47.raw.size = 53 ∧ s29_47.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.TinyccClosed.Identifier.Variants
