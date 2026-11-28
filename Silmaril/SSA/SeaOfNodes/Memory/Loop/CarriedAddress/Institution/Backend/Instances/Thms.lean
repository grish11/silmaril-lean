module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Thms

/-! The shared API agrees with both existing institutions and their comparison. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend

open CategoryTheory Silmaril.Logic.Institution
open Memory.Diamond.Institution renaming Signature → EntrySignature

variable {P Q : EntrySignature}

theorem rvsdg_room (P : EntrySignature) : rvsdg.room P = RuntimeRoom.room P := rfl

theorem memref_room (P : EntrySignature) : memref.room P = MemRefRoom.room P := rfl

theorem rvsdg_corridor (h : P ⟶ Q) : rvsdg.corridor h = RuntimeRoom.corridor h := rfl

theorem memref_corridor (h : P ⟶ Q) : memref.corridor h = MemRefRoom.corridor h := rfl

theorem rvsdg_inst : rvsdg.inst = RuntimeRoom.inst := rfl

theorem memref_inst : memref.inst = MemRefRoom.inst := rfl

theorem rvsdg_comparison : rvsdg.comparison = RuntimeRoom.comparison := rfl

theorem memref_comparison : memref.comparison = MemRefRoom.comparison := rfl

theorem rvsdg_memref_comparison : rvsdg.comparisonBetween memref = MemRefRoom.runtimeComparison := rfl

/-- The existing public comparison maps form the same comorphism triangle. -/
theorem rvsdg_memref_factors :
    Inst.CoHom.comp RuntimeRoom.comparison MemRefRoom.runtimeComparison = MemRefRoom.comparison :=
  comparison_factors rvsdg memref

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend
