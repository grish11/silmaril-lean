module
public import Silmaril.Elf.Corpus.MimallocClosed.AllocatorDone.Defs
import Silmaril.Proofs.Elf.Corpus.MimallocClosed.AllocatorDone
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocClosed.AllocatorDone
theorem elaborates : Silmaril.Project.Shapes.C.ElaboratesTo ail "_mi_allocator_done" sourceFn :=
  Silmaril.Proofs.Elf.Corpus.MimallocClosed.AllocatorDone.elaborates
open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21 in
theorem code_at : Silmaril.Elf.CodeAt F 0x17570 code :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
open Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21 in
theorem symbol_identity :
    s28_329.name = ("_mi_allocator_done".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s28_329.raw.value = 0x17570 ∧ s28_329.raw.size = 1 ∧ s28_329.kind = 2 := by
  decide +kernel
end Silmaril.Elf.Corpus.MimallocClosed.AllocatorDone
