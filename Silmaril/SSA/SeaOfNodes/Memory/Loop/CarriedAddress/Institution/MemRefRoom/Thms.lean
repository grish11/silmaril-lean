module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Observation
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Reindex

/-! Satisfaction and re-emission in the generated ordered MemRef room. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

theorem GeneratedProgram.observe_eq_some_iff (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (result : Word × Buffer model.cells) :
    program.observe model initial = Part.some result ↔ program.Returns model initial result :=
  Proofs.observe_eq_some_iff program model initial result

/-- A complete finite return of the emitted program is a native return
of the same word and every cell. -/
theorem GeneratedProgram.observe_eq_some_iff_native (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (result : Word × Buffer model.cells) :
    program.observe model initial = Part.some result ↔
      nativeReturns program.source model initial.cell result.1 result.2.cell :=
  Proofs.observe_eq_some_iff_native program model initial result

/-- The full buffer observation is absent exactly when there is no finite native return. -/
theorem GeneratedProgram.observe_eq_none_iff (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) :
    program.observe model initial = Part.none ↔ (nativeReturns program.source model).NoReturn initial.cell :=
  Proofs.observe_eq_none_iff program model initial

/-- Encode the returned word and every cell into the existing RVSDG result
tuple. Both observers use their own finite execution witnesses. -/
theorem observe_runtime (graph : Graph P.args) (model : EntryModel P) (initial : Buffer model.cells) :
    ((GeneratedProgram.lower graph).observe model initial).map (fun result => encodeResult result.1 result.2.cell) =
      RuntimeEntry.observe graph (RuntimeRoom.modelEntry model initial.cell).val :=
  Proofs.observe_runtime graph model initial

theorem GeneratedProgram.observe_map (h : P ⟶ Q) (program : GeneratedProgram P.args)
    (model : EntryModel Q) (initial : Buffer model.cells) :
    (program.map h).observe model initial = program.observe (reduct h model) initial :=
  Proofs.observe_map h program model initial

@[simp] theorem Sentence.map_id (e : Sentence P) : e.map (𝟙 P) = e :=
  Proofs.map_id e

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Sentence P) :
    e.map (h ≫ k) = (e.map h).map k :=
  Proofs.map_comp h k e

theorem Sentence.satisfaction_map (h : P ⟶ Q) (e : Sentence P) (model : EntryModel Q) :
    (e.map h).Holds model ↔ e.Holds (reduct h model) :=
  Proofs.satisfaction_map h e model

theorem lowerEquation_map (h : P ⟶ Q) (e : Equation P) :
    (lowerEquation e).map h = lowerEquation (e.map h) :=
  rfl

theorem satisfaction (e : Equation P) (model : EntryModel P) :
    (lowerEquation e).Holds model ↔ e.Holds model :=
  Proofs.satisfaction e model

/-- After re-emission, truth at every target valuation compares against
native truth over the image of the typed valuation pullback. -/
theorem all_models_map_iff (h : P ⟶ Q) (e : Equation P) (cells : Nat) :
    (∀ input : Tuple (Val cells) Q.args, (lowerEquation (e.map h)).Holds (⟨cells, input⟩ : EntryModel Q)) ↔
      ∀ input : Tuple (Val cells) Q.args, e.Holds (reduct h (⟨cells, input⟩ : EntryModel Q)) :=
  forall_congr' fun input => (satisfaction (e.map h) ⟨cells, input⟩).trans (e.satisfaction h ⟨cells, input⟩)

def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Sentence.map h, (Institution.corridor h).mod, fun m e => e.satisfaction_map h m.as⟩

theorem corridor_id (P : EntrySignature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Sentence.map_id)
    (congrArg (fun f : Institution.room P ⟶ Institution.room P => f.mod) (Institution.corridor_id P))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) : corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Sentence.map_comp h k))
    (congrArg (fun f : Institution.room P ⟶ Institution.room R => f.mod) (Institution.corridor_comp h k))

def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

def comparisonCorridor (P : EntrySignature) : Institution.room P ⟶ room P :=
  ⟨lowerEquation, 𝟭 _, fun m e => satisfaction e m.as⟩

theorem comparison_natural (h : P ⟶ Q) :
    Institution.corridor h ≫ comparisonCorridor Q = comparisonCorridor P ≫ corridor h :=
  Room.hom_ext (funext fun e => (lowerEquation_map h e).symm)
    (Discrete.functor_ext fun _ => rfl)

/-- The native equations map to the generated MemRef room over the same
typed entry signatures. -/
def comparison : Inst.CoHom Institution.inst inst where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor
         naturality := fun {P Q} h => comparison_natural (P := P) (Q := Q) h }

/-- Re-emit the sources retained by the generated RVSDG sentence. -/
def fromRuntime (e : RuntimeRoom.Sentence P) : Sentence P :=
  lowerEquation ⟨e.lhs.source, e.rhs.source⟩

theorem fromRuntime_satisfaction (e : RuntimeRoom.Sentence P) (model : EntryModel P) :
    (fromRuntime e).Holds model ↔ e.Holds model := by
  obtain ⟨⟨left, _, rfl⟩, ⟨right, _, rfl⟩⟩ := e
  exact (satisfaction ⟨left, right⟩ model).trans (RuntimeRoom.satisfaction ⟨left, right⟩ model).symm

def runtimeCorridor (P : EntrySignature) : RuntimeRoom.room P ⟶ room P :=
  ⟨fromRuntime, 𝟭 _, fun m e => fromRuntime_satisfaction e m.as⟩

theorem runtimeCorridor_natural (h : P ⟶ Q) :
    RuntimeRoom.corridor h ≫ runtimeCorridor Q = runtimeCorridor P ≫ corridor h :=
  Room.hom_ext rfl (Discrete.functor_ext fun _ => rfl)

/-- Compare the generated backend Rooms via their common native sources. -/
def runtimeComparison : Inst.CoHom RuntimeRoom.inst inst where
  Φ := 𝟭 _
  ρ := { app := runtimeCorridor
         naturality := fun {P Q} h => runtimeCorridor_natural (P := P) (Q := Q) h }

theorem comparison_factors (P : EntrySignature) :
    RuntimeRoom.comparisonCorridor P ≫ runtimeCorridor P = comparisonCorridor P :=
  Room.hom_ext rfl (Discrete.functor_ext fun _ => rfl)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom
