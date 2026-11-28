module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Reindex

/-! The emitted runtime room and the comparison over typed entry signatures. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

@[simp] theorem Sentence.map_id (e : Sentence P) : e.map (𝟙 P) = e :=
  Proofs.map_id e

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Sentence P) :
    e.map (h ≫ k) = (e.map h).map k :=
  Proofs.map_comp h k e

/-- The admissible entry at this valuation and heap is exactly the raw
tuple that decodes to them. -/
theorem decode_eq_modelEntry_iff (model : EntryModel P) (heap : Heap model.cells)
    (raw : RuntimeEntry.RawEntry P.args model.cells) :
    RuntimeEntry.decode raw = some ⟨model.input, heap⟩ ↔ (modelEntry model heap).val = raw :=
  RuntimeEntry.decode_eq_some_iff _ _

/-- The target model's admissible entries pull back with the valuation
while keeping the occurrence and each initialized heap. -/
theorem modelEntry_reindex (h : P ⟶ Q) (model : EntryModel Q) (heap : Heap model.cells) :
    RuntimeEntry.reindex h (modelEntry model heap).val = (modelEntry (reduct h model) heap).val :=
  Proofs.modelEntry_reindex h model heap

/-- Re-emission preserves the exact partial observation at the reduct. -/
theorem GeneratedProgram.observe_map (h : P ⟶ Q) (program : GeneratedProgram P.args)
    (model : EntryModel Q) (heap : Heap model.cells) :
    RuntimeEntry.observeProgram (program.map h).program (modelEntry model heap).val =
      RuntimeEntry.observeProgram program.program (modelEntry (reduct h model) heap).val :=
  Proofs.observe_map h program model heap

theorem Sentence.satisfaction_map (h : P ⟶ Q) (e : Sentence P) (model : EntryModel Q) :
    (e.map h).Holds model ↔ e.Holds (reduct h model) :=
  Proofs.satisfaction_map h e model

theorem lowerEquation_map (h : P ⟶ Q) (e : Equation P) :
    (lowerEquation e).map h = lowerEquation (e.map h) :=
  rfl

/-- At one runtime model the generated equation holds exactly when the
native equation holds at that cell count and valuation. -/
theorem satisfaction (e : Equation P) (model : EntryModel P) :
    (lowerEquation e).Holds model ↔ e.Holds model :=
  runtime_satisfaction e model

/-- The room's global comparison at a cell count ranges over all its
typed valuations and consequently over all admissible raw entries. -/
theorem holds_iff_all_models (e : Equation P) (cells : Nat) :
    RuntimeEntry.Holds e cells ↔ ∀ input : Tuple (Val cells) P.args,
      (lowerEquation e).Holds (⟨cells, input⟩ : EntryModel P) :=
  (RuntimeEntry.satisfaction e cells).trans
    (forall_congr' fun input => (satisfaction e ⟨cells, input⟩).symm)

/-- The global reindexed comparison ranges over the image of the target
valuation reduct. A port map can identify distinct source ports. -/
theorem holds_map_iff_reduct_models (h : P ⟶ Q) (e : Equation P) (cells : Nat) :
    RuntimeEntry.Holds (e.map h) cells ↔ ∀ input : Tuple (Val cells) Q.args,
      (lowerEquation e).Holds (reduct h (⟨cells, input⟩ : EntryModel Q)) :=
  (RuntimeEntry.satisfaction_reindex h e cells).trans
    (forall_congr' fun input => (satisfaction e (reduct h ⟨cells, input⟩)).symm)

theorem satisfaction_iff_petri (e : Equation P) (model : EntryModel P) :
    (lowerEquation e).Holds model ↔ petriHolds e model :=
  (satisfaction e model).trans (petri_satisfaction e model).symm

theorem satisfaction_iff_memref (e : Equation P) (model : EntryModel P) :
    (lowerEquation e).Holds model ↔ memrefHolds e model :=
  (satisfaction e model).trans (memref_satisfaction e model).symm

/-- A typed port map from P to Q re-emits sentences forward and pulls
entry models back from Q to P. -/
def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Sentence.map h, (Institution.corridor h).mod, fun m e => e.satisfaction_map h m.as⟩

theorem corridor_id (P : EntrySignature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Sentence.map_id)
    (congrArg (fun f : Institution.room P ⟶ Institution.room P => f.mod) (Institution.corridor_id P))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) : corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Sentence.map_comp h k))
    (congrArg (fun f : Institution.room P ⟶ Institution.room R => f.mod) (Institution.corridor_comp h k))

/-- The institution of generated runtime equations over typed entry maps. -/
def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

def comparisonCorridor (P : EntrySignature) : Institution.room P ⟶ room P :=
  ⟨lowerEquation, 𝟭 _, fun m e => satisfaction e m.as⟩

theorem comparison_natural (h : P ⟶ Q) :
    Institution.corridor h ≫ comparisonCorridor Q = comparisonCorridor P ≫ corridor h :=
  Room.hom_ext (funext fun e => (lowerEquation_map h e).symm)
    (Discrete.functor_ext fun _ => rfl)

/-- The native equations map to the generated runtime room over the
same typed memory entry signature category. -/
def comparison : Inst.CoHom Institution.inst inst where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor, naturality := fun {P Q} h => comparison_natural (P := P) (Q := Q) h }

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom
