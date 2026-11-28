module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Observation

/-! The native-to-MemRef comorphism and its canonical numbered comparison. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

theorem GeneratedProgram.returns_iff_native (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (word : Word) (final : Buffer model.cells) :
    program.Returns model initial (word, final) ↔
      nativeReturns program.source model initial.cell word final.cell :=
  Proofs.returns_iff_native program model initial word final

/-- The numbered observer uses the canonical runtime and the same typed
valuation. The finite witnesses have independent bounds. -/
theorem GeneratedProgram.returns_iff_numbered (program : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Buffer model.cells) (word : Word) (final : Buffer model.cells) :
    program.Returns model initial (word, final) ↔
      runtimeObserve program.source model initial.cell = Part.some (encodeResult word final.cell) :=
  (program.returns_iff_native model initial word final).trans
    (runtimeObserve_eq_some_iff_native program.source model initial.cell word final.cell).symm

@[simp] theorem Sentence.source_lower (s : Institution.Sentence P) : (lower s).source = s := by
  cases s <;> rfl

@[simp] theorem Sentence.lower_source (s : Sentence P) : lower s.source = s :=
  Proofs.lower_source s

@[simp] theorem Sentence.map_id (s : Sentence P) : s.map (𝟙 P) = s := by
  rw [map, Institution.Sentence.map_id, lower_source]

theorem Sentence.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (s : Sentence P) :
    s.map (h ≫ k) = (s.map h).map k := by
  simp only [map, source_lower, Institution.Sentence.map_comp]

/-- Both equations and termination are checked against the stored CFGs. -/
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
  ((lower s).satisfaction model).trans (iff_of_eq (congrArg (fun source => source.Holds model) (source_lower s)))

def comparisonCorridor (P : EntrySignature) : Institution.room P ⟶ room P :=
  ⟨Sentence.lower, 𝟭 _, fun m s => Sentence.lower_satisfaction s m.as⟩

theorem comparison_natural (h : P ⟶ Q) :
    Institution.corridor h ≫ comparisonCorridor Q = comparisonCorridor P ≫ corridor h :=
  Room.hom_ext (funext fun s => congrArg (fun source : Institution.Sentence P => Sentence.lower (source.map h))
    (Sentence.source_lower s).symm) (Discrete.functor_ext fun _ => rfl)

/-- Both institutions have the same typed capture signatures. -/
def comparison : Inst.CoHom Institution.inst inst where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor
         naturality := fun {P Q} h => comparison_natural (P := P) (Q := Q) h }

theorem Sentence.numbered_map (h : P ⟶ Q) (s : Sentence P) :
    (s.map h).numbered = translate (s.source.map h) := by
  simp only [numbered, map, source_lower]

/-- Restrict the numbered observer to the same typed valuation and vary
the initialized heap. Both native sentence forms use this comparison. -/
theorem Sentence.numbered_satisfaction_at_model (s : Sentence P) (model : EntryModel P) :
    s.Holds model ↔ s.source.HoldsWith (fun graph initial word final =>
      runtimeObserve graph model initial = Part.some (encodeResult word final)) :=
  (s.satisfaction model).trans (by cases s.source <;>
    simp only [Institution.Sentence.Holds, Institution.Sentence.HoldsWith, runtimeObserve_eq_some_iff_native])

/-- In the existing numbered room, satisfaction at the canonical runtime
is equivalent to emitted MemRef satisfaction at all valuations of that size. -/
theorem Sentence.numbered_satisfaction (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) s.numbered ↔
      ∀ input : Tuple (Val cells) P.args, s.Holds ⟨cells, input⟩ :=
  (Institution.numbered_satisfaction s.source cells).trans
    (forall_congr' fun input => (s.satisfaction ⟨cells, input⟩).symm)

/-- After re-emission, global numbered truth ranges over the image of the
typed valuation reduct. Identifying source ports can restrict that image. -/
theorem Sentence.numbered_satisfaction_map (h : P ⟶ Q) (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (s.map h).numbered ↔
      ∀ input : Tuple (Val cells) Q.args, s.Holds (reduct h ⟨cells, input⟩) :=
  ((s.map h).numbered_satisfaction cells).trans (forall_congr' fun input => s.satisfaction_map h ⟨cells, input⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom
