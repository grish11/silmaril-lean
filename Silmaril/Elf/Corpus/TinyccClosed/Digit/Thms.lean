module
public import Silmaril.Elf.Corpus.TinyccClosed.Digit.Defs
import Silmaril.Proofs.Elf.Corpus.TinyccClosed.Digit
@[expose] public section
namespace Silmaril.Elf.Corpus.TinyccClosed.Digit
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "isnum" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.TinyccClosed.Digit.elaborates
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem code_at : Silmaril.Elf.CodeAt F 0x753b code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem symbol_identity :
    s29_52.name = ("isnum".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s29_52.raw.value = 0x753b ∧ s29_52.raw.size = 33 ∧ s29_52.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.TinyccClosed.Digit
