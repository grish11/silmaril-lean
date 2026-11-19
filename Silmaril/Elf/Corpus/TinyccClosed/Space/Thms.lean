module
public import Silmaril.Elf.Corpus.TinyccClosed.Space.Defs
import Silmaril.Proofs.Elf.Corpus.TinyccClosed.Space
@[expose] public section
namespace Silmaril.Elf.Corpus.TinyccClosed.Space
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "is_space" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.TinyccClosed.Space.elaborates
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem code_at : Silmaril.Elf.CodeAt F 0x74d5 code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem symbol_identity :
    s29_50.name = ("is_space".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s29_50.raw.value = 0x74d5 ∧ s29_50.raw.size = 51 ∧ s29_50.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.TinyccClosed.Space
