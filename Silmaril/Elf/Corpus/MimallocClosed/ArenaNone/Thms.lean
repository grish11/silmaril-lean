module
public import Silmaril.Elf.Corpus.MimallocClosed.ArenaNone.Defs
import Silmaril.Proofs.Elf.Corpus.MimallocClosed.ArenaNone
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocClosed.ArenaNone
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "_mi_arena_id_none" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.MimallocClosed.ArenaNone.elaborates
open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21 in
theorem code_at : Silmaril.Elf.CodeAt F 0x9b20 code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21 in
theorem symbol_identity :
    s28_252.name = ("_mi_arena_id_none".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_252.raw.value = 0x9b20 ∧ s28_252.raw.size = 3 ∧ s28_252.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.MimallocClosed.ArenaNone
