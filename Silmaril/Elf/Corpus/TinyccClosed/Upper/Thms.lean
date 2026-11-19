module
public import Silmaril.Elf.Corpus.TinyccClosed.Upper.Defs
import Silmaril.Proofs.Elf.Corpus.TinyccClosed.Upper
@[expose] public section
namespace Silmaril.Elf.Corpus.TinyccClosed.Upper
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "toup" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.TinyccClosed.Upper.elaborates
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem code_at : Silmaril.Elf.CodeAt F 0x757d code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem symbol_identity :
    s29_54.name = ("toup".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s29_54.raw.value = 0x757d ∧ s29_54.raw.size = 32 ∧ s29_54.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.TinyccClosed.Upper
