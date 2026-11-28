module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Proofs

open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature}

theorem returns_iff_native (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (word : Word) (final : Buffer model.cells) :
    program.Returns model initial (word, final) ↔
      nativeReturns program.source model initial.cell word final.cell := by
  obtain ⟨source, _, rfl⟩ := program
  exact MemRef.returns_iff source model.input initial.cell word final.cell

theorem lower_source (s : Sentence P) : Sentence.lower s.source = s := by
  cases s with
  | equation lhs rhs =>
    obtain ⟨_, _, rfl⟩ := lhs
    obtain ⟨_, _, rfl⟩ := rhs
    rfl
  | terminates p =>
    obtain ⟨_, _, rfl⟩ := p
    rfl

theorem satisfaction (s : Sentence P) (model : EntryModel P) : s.Holds model ↔ s.source.Holds model := by
  cases s with
  | equation lhs rhs =>
    constructor
    · intro agrees heap word final
      exact ((returns_iff_native lhs model ⟨heap⟩ word ⟨final⟩).symm.trans (agrees ⟨heap⟩ word ⟨final⟩)).trans
        (returns_iff_native rhs model ⟨heap⟩ word ⟨final⟩)
    · intro agrees initial word final
      exact ((returns_iff_native lhs model initial word final).trans (agrees initial.cell word final.cell)).trans
        (returns_iff_native rhs model initial word final).symm
  | terminates program =>
    constructor
    · intro total heap
      obtain ⟨word, final, returned⟩ := total ⟨heap⟩
      exact ⟨word, final.cell, (returns_iff_native program model ⟨heap⟩ word final).mp returned⟩
    · intro total initial
      obtain ⟨word, heap, returned⟩ := total initial.cell
      exact ⟨word, ⟨heap⟩, (returns_iff_native program model initial word ⟨heap⟩).mpr returned⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Proofs
