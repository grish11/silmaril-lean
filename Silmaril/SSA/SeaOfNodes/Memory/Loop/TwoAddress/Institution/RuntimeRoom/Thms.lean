module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Observation

/-! Native-to-numbered comparison over typed entry signatures. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

theorem GeneratedProgram.observe_eq_runtime (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    p.observe model initial = runtimeObserve p.source model initial :=
  Proofs.observe_eq_runtime p model initial

theorem GeneratedProgram.observe_eq_some_iff_native (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    p.observe model initial = Part.some (encodeResult word final) ↔
      nativeReturns p.source model initial word final :=
  Proofs.observe_eq_some_iff_native p model initial word final

/-- Re-emission compares the whole partial value at the reduct, including
absence of a finite return. -/
theorem GeneratedProgram.observe_map (h : P ⟶ Q) (p : GeneratedProgram P.args) (model : EntryModel Q)
    (initial : Heap model.cells) :
    (p.map h).observe model initial = p.observe (reduct h model) initial :=
  Proofs.observe_map h p model initial

@[simp] theorem Sentence.source_lower (s : Institution.Sentence P) : (lower s).source = s := by
  cases s <;> rfl

@[simp] theorem Sentence.lower_source (s : Sentence P) : lower s.source = s :=
  Proofs.lower_source s

@[simp] theorem Sentence.map_id (s : Sentence P) : s.map (𝟙 P) = s := by
  rw [map, Institution.Sentence.map_id, lower_source]

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k := by
  simp only [map, source_lower, Institution.Sentence.map_comp]

theorem Sentence.numbered_eq_translate (s : Sentence P) : s.numbered = translate s.source :=
  Proofs.numbered_eq_translate s

theorem Sentence.satisfaction (s : Sentence P) (model : EntryModel P) :
    s.Holds model ↔ s.source.Holds model :=
  Proofs.satisfaction s model

theorem Sentence.satisfaction_map (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    (s.map h).Holds model ↔ s.Holds (reduct h model) := by
  rw [satisfaction, map, source_lower, Institution.Sentence.satisfaction_map, ← satisfaction]

def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨Sentence.map h, (Institution.corridor h).mod, fun m s => s.satisfaction_map h m.as⟩

theorem corridor_id (P : EntrySignature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext (funext Sentence.map_id)
    (congrArg (fun f : Institution.room P ⟶ Institution.room P => f.mod) (Institution.corridor_id P))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) : corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext (funext (Sentence.map_comp h k))
    (congrArg (fun f : Institution.room P ⟶ Institution.room R => f.mod) (Institution.corridor_comp h k))

def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

theorem Sentence.lower_satisfaction (s : Institution.Sentence P) (model : EntryModel P) :
    (lower s).Holds model ↔ s.Holds model :=
  ((lower s).satisfaction model).trans (iff_of_eq (congrArg (·.Holds model) (source_lower s)))

def comparisonCorridor (P : EntrySignature) : Institution.room P ⟶ room P :=
  ⟨Sentence.lower, 𝟭 _, fun m s => Sentence.lower_satisfaction s m.as⟩

theorem comparison_natural (h : P ⟶ Q) :
    Institution.corridor h ≫ comparisonCorridor Q = comparisonCorridor P ≫ corridor h :=
  Room.hom_ext (funext fun s => congrArg (fun source : Institution.Sentence P => Sentence.lower (source.map h))
    (Sentence.source_lower s).symm) (Discrete.functor_ext fun _ => rfl)

/-- Native sentences map to generated numbered programs over the same
capture signatures and typed valuation models. -/
def comparison : Inst.CoHom Institution.inst inst where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor
         naturality := fun {P Q} h => comparison_natural (P := P) (Q := Q) h }

/-- The existing room at the canonical runtime ranges over all valuations
at a cell count. Generated-room models each fix one such valuation. -/
theorem Sentence.numbered_satisfaction (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) s.numbered ↔
      ∀ input : Tuple (Val cells) P.args, s.Holds ⟨cells, input⟩ := by
  rw [numbered_eq_translate]
  exact (Institution.numbered_satisfaction s.source cells).trans
    (forall_congr' fun input => (s.satisfaction ⟨cells, input⟩).symm)

/-- For a capture map that identifies ports, global truth after re-emission
quantifies over the valuations pulled back from the target. -/
theorem Sentence.numbered_satisfaction_map (h : P ⟶ Q) (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (s.map h).numbered ↔
      ∀ input : Tuple (Val cells) Q.args, s.Holds (reduct h ⟨cells, input⟩) :=
  ((s.map h).numbered_satisfaction cells).trans (forall_congr' fun input => s.satisfaction_map h ⟨cells, input⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom
