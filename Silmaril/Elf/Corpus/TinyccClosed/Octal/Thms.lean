module
public import Silmaril.Elf.Corpus.TinyccClosed.Octal.Defs
import Silmaril.Proofs.Elf.Corpus.TinyccClosed.Octal
@[expose] public section
namespace Silmaril.Elf.Corpus.TinyccClosed.Octal
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "isoct" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.TinyccClosed.Octal.elaborates
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem code_at : Silmaril.Elf.CodeAt F 0x755c code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem symbol_identity :
    s29_53.name = ("isoct".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s29_53.raw.value = 0x755c ∧ s29_53.raw.size = 33 ∧ s29_53.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.TinyccClosed.Octal
