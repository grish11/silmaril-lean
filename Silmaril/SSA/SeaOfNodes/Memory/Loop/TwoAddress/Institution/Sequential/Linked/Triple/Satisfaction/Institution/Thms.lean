module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Check.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Institution.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

/-! Institutions over typed capture maps and comparison of their generated backends. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open CarriedAddress.Institution.RuntimeEntry (Entry)
open Linked.Satisfaction.ReductImage
  (liftThrough? liftThrough?_sound checkCompositeCoverage checkCompositeCoverage_iff
    checkCompositeExpansive checkCompositeExpansive_eq)
open Memory.Diamond.Institution (reduct reduct_id reduct_comp)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

@[simp] theorem Program.map_id (p : Program P) : p.map (𝟙 P) = p :=
  InstitutionProofs.program_map_id p

theorem Program.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P) :
    p.map (h ≫ k) = (p.map h).map k :=
  InstitutionProofs.program_map_comp h k p

@[simp] theorem Sentence.map_id (s : Sentence P) : s.map (𝟙 P) = s := by
  cases s <;> simp only [Sentence.map, Program.map_id]

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k := by
  cases s <;> simp only [Sentence.map, Program.map_comp]

/-- All three model relations compare the same three ordered words and heap. -/
theorem Backend.holds_iff_numbered (backend : Backend) (s : Sentence P) (model : EntryModel P) :
    backend.Holds s model ↔ s.NumberedHolds model := by
  cases backend
  · rfl
  · exact s.memref_satisfaction model
  · exact s.coloured_satisfaction model

theorem Backend.satisfaction_map (backend : Backend) (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    backend.Holds (s.map h) model ↔ backend.Holds s (reduct h model) :=
  (backend.holds_iff_numbered (s.map h) model).trans
    ((s.satisfaction_map h model).trans (backend.holds_iff_numbered s (reduct h model)).symm)

/-- Satisfaction of the staged re-emission at a checked target entry
agrees with source satisfaction at the lifted valuation's reduct. -/
theorem Backend.satisfaction_liftThrough (backend : Backend) (h : P ⟶ Q) (k : Q ⟶ R)
    (s : Sentence P) {cells : Nat} {entry : Entry P.args cells} {between : Entry Q.args cells}
    {target : Entry R.args cells} (lifted : liftThrough? h k entry = some (between, target)) :
    backend.Holds ((s.map h).map k) target.model ↔ backend.Holds s entry.model := by
  have stages := liftThrough?_sound h k lifted
  have pulled : reduct h (reduct k target.model) = entry.model :=
    congrArg (Entry.model (P := P)) ((congrArg (Entry.reduct h) stages.2).trans stages.1)
  exact (backend.satisfaction_map k (s.map h) target.model).trans
    ((backend.satisfaction_map h s (reduct k target.model)).trans (iff_of_eq (congrArg (backend.Holds s) pulled)))

/-- Re-emit sentences along a typed port map and pull valuations back along it. -/
def corridor (backend : Backend) (h : P ⟶ Q) : room backend P ⟶ room backend Q :=
  ⟨Sentence.map h, modelReduct backend h, fun m s => backend.satisfaction_map h s m.as⟩

theorem corridor_id (backend : Backend) (P : EntrySignature) :
    corridor backend (𝟙 P) = 𝟙 (room backend P) :=
  Room.hom_ext (funext Sentence.map_id) (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_id m))

theorem corridor_comp (backend : Backend) (h : P ⟶ Q) (k : Q ⟶ R) :
    corridor backend (h ≫ k) = corridor backend h ≫ corridor backend k :=
  Room.hom_ext (funext (Sentence.map_comp h k))
    (Discrete.functor_ext fun m => congrArg Discrete.mk (reduct_comp h k m))

def inst (backend : Backend) : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨room backend, corridor backend, corridor_id backend, corridor_comp backend⟩

/-- Interpret the same canonical typed sentence and valuation at another backend. -/
def comparisonCorridor (source target : Backend) (P : EntrySignature) : room source P ⟶ room target P :=
  ⟨id, 𝟭 _, fun m s => (target.holds_iff_numbered s m.as).trans (source.holds_iff_numbered s m.as).symm⟩

theorem comparison_natural (source target : Backend) (h : P ⟶ Q) :
    corridor source h ≫ comparisonCorridor source target Q = comparisonCorridor source target P ≫ corridor target h :=
  Room.hom_ext rfl (Discrete.functor_ext fun _ => rfl)

/-- The generated institutions have identity translations on signatures,
sentences and typed models. Their satisfaction uses actual backend execution. -/
def comparison (source target : Backend) : Inst.CoHom (inst source) (inst target) where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor source target
         naturality := fun {P Q} h => comparison_natural (P := P) (Q := Q) source target h }

/-- The corridor is model-expansive exactly when every source valuation
at every cell count lies in the reduct image. -/
theorem corridor_modelExpansive_iff (backend : Backend) (h : P ⟶ Q) :
    (corridor backend h).ModelExpansive ↔
      ∀ cells (input : Tuple (Val cells) P.args), Linked.Satisfaction.InReductImage h input :=
  InstitutionProofs.modelReduct_surjective_iff backend h

theorem corridor_modelExpansive_of_retraction (backend : Backend) (h : P ⟶ Q) (back : Q ⟶ P)
    (split : h ≫ back = 𝟙 P) : (corridor backend h).ModelExpansive :=
  (corridor_modelExpansive_iff backend h).mpr fun _ => Linked.Satisfaction.in_image_of_retraction h back split

/-- The typed-port check decides model coverage for each generated backend. -/
theorem corridor_modelExpansive_iff_check (backend : Backend) (h : P ⟶ Q) :
    (corridor backend h).ModelExpansive ↔ Linked.Satisfaction.ReductImage.checkExpansive h = true :=
  (corridor_modelExpansive_iff backend h).trans (Linked.Satisfaction.ReductImage.checkExpansive_iff h).symm

theorem corridor_comp_modelExpansive_iff_check (backend : Backend) (h : P ⟶ Q) (k : Q ⟶ R) :
    (corridor backend h ≫ corridor backend k).ModelExpansive ↔ checkCompositeExpansive h k = true := by
  rw [← corridor_comp, checkCompositeExpansive_eq, corridor_modelExpansive_iff_check]

/-- The existing numbered room's all-target truth, after re-emission, is
exactly backend truth on source valuations in the typed reduct image. -/
theorem Sentence.room_satisfaction_image (s : Sentence P) (backend : Backend) (h : P ⟶ Q) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (s.map h).numbered ↔
      ∀ input : Tuple (Val cells) P.args, Linked.Satisfaction.InReductImage h input →
        backend.Holds s ⟨cells, input⟩ :=
  (s.room_satisfaction_map h cells).trans
    ((Linked.Satisfaction.forall_reduct_image h s.NumberedHolds).trans
      (forall_congr' fun input => forall_congr' fun _ => (backend.holds_iff_numbered s ⟨cells, input⟩).symm))

/-- Checked coverage at this count permits quantifying over every source
valuation in the staged re-emission's satisfaction condition. -/
theorem Sentence.room_satisfaction_comp_of_check (s : Sentence P) (backend : Backend)
    (h : P ⟶ Q) (k : Q ⟶ R) (cells : Nat) (covered : checkCompositeCoverage h k cells = true) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells))
        ((s.map h).map k).numbered ↔
      ∀ input : Tuple (Val cells) P.args, backend.Holds s ⟨cells, input⟩ := by
  rw [← s.map_comp h k, s.room_satisfaction_image backend (h ≫ k) cells]
  exact ⟨fun holds input => holds input ((checkCompositeCoverage_iff h k cells).mp covered input),
    fun holds input _ => holds input⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction
