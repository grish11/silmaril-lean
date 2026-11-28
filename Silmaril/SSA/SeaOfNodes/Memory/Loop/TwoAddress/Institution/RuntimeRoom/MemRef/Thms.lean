module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Thms

/-! The generated numbered and MemRef institutions compare through their retained sources. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature}

/-- A finite MemRef observation and the stored numbered program observe
the same word and entire heap with independent execution witnesses. -/
theorem GeneratedProgram.memref_returns_iff (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (word : Word) (final : Buffer model.cells) :
    (MemRefRoom.GeneratedProgram.lower p.source).Returns model initial (word, final) ↔
      p.observe model initial.cell = Part.some (encodeResult word final.cell) :=
  ((MemRefRoom.GeneratedProgram.lower p.source).returns_iff_numbered model initial word final).trans
    (iff_of_eq (congrArg (· = Part.some (encodeResult word final.cell)) (p.observe_eq_runtime model initial.cell).symm))

def Sentence.toMemRef (s : Sentence P) : MemRefRoom.Sentence P :=
  MemRefRoom.Sentence.lower s.source

theorem Sentence.toMemRef_numbered (s : Sentence P) : s.toMemRef.numbered = s.numbered :=
  (congrArg translate (MemRefRoom.Sentence.source_lower s.source)).trans s.numbered_eq_translate.symm

theorem Sentence.toMemRef_satisfaction (s : Sentence P) (model : EntryModel P) :
    s.toMemRef.Holds model ↔ s.Holds model :=
  (MemRefRoom.Sentence.lower_satisfaction s.source model).trans (s.satisfaction model).symm

theorem Sentence.toMemRef_satisfaction_map (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    (s.toMemRef.map h).Holds model ↔ s.Holds (reduct h model) :=
  (s.toMemRef.satisfaction_map h model).trans (s.toMemRef_satisfaction (reduct h model))

theorem Sentence.toMemRef_map (h : P ⟶ Q) (s : Sentence P) :
    (s.map h).toMemRef = s.toMemRef.map h := by
  simp only [toMemRef, Sentence.map, Sentence.source_lower, MemRefRoom.Sentence.map, MemRefRoom.Sentence.source_lower]

def toMemRefCorridor (P : EntrySignature) : room P ⟶ MemRefRoom.room P :=
  ⟨Sentence.toMemRef, 𝟭 _, fun m s => s.toMemRef_satisfaction m.as⟩

theorem toMemRef_natural (h : P ⟶ Q) :
    corridor h ≫ toMemRefCorridor Q = toMemRefCorridor P ≫ MemRefRoom.corridor h :=
  Room.hom_ext (funext (Sentence.toMemRef_map h)) (Discrete.functor_ext fun _ => rfl)

/-- Compare the two generated institutions at the same typed models. -/
def toMemRefComparison : Inst.CoHom inst MemRefRoom.inst where
  Φ := 𝟭 _
  ρ := { app := toMemRefCorridor
         naturality := fun {P Q} h => toMemRef_natural (P := P) (Q := Q) h }

theorem comparisonCorridor_factors (P : EntrySignature) :
    comparisonCorridor P ≫ toMemRefCorridor P = MemRefRoom.comparisonCorridor P :=
  Room.hom_ext (funext fun s => congrArg MemRefRoom.Sentence.lower (Sentence.source_lower s))
    (Discrete.functor_ext fun _ => rfl)

/-- Lowering through the generated numbered institution gives the same
comorphism into MemRef as the direct native comparison. -/
theorem comparison_factors : Inst.CoHom.comp comparison toMemRefComparison = MemRefRoom.comparison :=
  Inst.CoHom.ext rfl (NatTrans.ext (funext comparisonCorridor_factors))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom
