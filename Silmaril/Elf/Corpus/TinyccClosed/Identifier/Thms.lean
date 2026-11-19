module
public import Silmaril.Elf.Corpus.TinyccClosed.Identifier.Defs
import Silmaril.Proofs.Elf.Corpus.TinyccClosed.Identifier
@[expose] public section
namespace Silmaril.Elf.Corpus.TinyccClosed.Identifier
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "isid" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.TinyccClosed.Identifier.elaborates
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem code_at : Silmaril.Elf.CodeAt F 0x7508 code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph3)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.CorpusVariants.Tinycc.N0927.Default.X8664.O0.Unstripped.Tcc in
theorem symbol_identity :
    s29_51.name = ("isid".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s29_51.raw.value = 0x7508 ∧ s29_51.raw.size = 51 ∧ s29_51.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.TinyccClosed.Identifier
