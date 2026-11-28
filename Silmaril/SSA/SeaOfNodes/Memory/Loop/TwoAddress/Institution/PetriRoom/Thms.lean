module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Observation

/-! Coloured and numbered satisfaction for the same generated sentences. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature}

theorem GeneratedProgram.completes_iff_numbered (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (output : Tuple (WireVal model.cells) (Threaded wordPorts)) :
    p.Completes model initial output ↔ p.observe model initial = Part.some output :=
  PetriRoom.Proofs.completes_iff_numbered p model initial output

/-- The complete partial values agree. The coloured observer has its own
finite firing witness, independent of the numbered evaluation bound. -/
theorem GeneratedProgram.petriObserve_eq_numbered (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) : p.petriObserve model initial = p.observe model initial :=
  PetriRoom.Proofs.petriObserve_eq_numbered p model initial

theorem GeneratedProgram.petriObserve_eq_some_iff (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) (output : Tuple (WireVal model.cells) (Threaded wordPorts)) :
    p.petriObserve model initial = Part.some output ↔ p.Completes model initial output := by
  rw [p.petriObserve_eq_numbered, p.completes_iff_numbered]

/-- An absent observation means there is no finite completed firing. -/
theorem GeneratedProgram.petriObserve_eq_none_iff (p : GeneratedProgram P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    p.petriObserve model initial = Part.none ↔ ∀ output, ¬ p.Completes model initial output := by
  rw [Part.eq_none_iff']
  exact not_exists

/-- The entire coloured observation commutes with re-emission at the
pulled-back typed valuation, including absence. -/
theorem GeneratedProgram.petriObserve_map (h : P ⟶ Q) (p : GeneratedProgram P.args) (model : EntryModel Q)
    (initial : Heap model.cells) :
    (p.map h).petriObserve model initial = p.petriObserve (reduct h model) initial :=
  ((p.map h).petriObserve_eq_numbered model initial).trans
    ((p.observe_map h model initial).trans (p.petriObserve_eq_numbered (reduct h model) initial).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.RuntimeRoom

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

/-- Equations and universal finite termination agree for the two
observers of the generated programs. -/
theorem holds_iff_numbered (s : RuntimeRoom.Sentence P) (model : EntryModel P) :
    Holds s model ↔ s.Holds model :=
  Proofs.holds_iff_numbered s model

theorem holds_map (h : P ⟶ Q) (s : RuntimeRoom.Sentence P) (model : EntryModel Q) :
    Holds (s.map h) model ↔ Holds s (reduct h model) :=
  (holds_iff_numbered (s.map h) model).trans
    ((s.satisfaction_map h model).trans (holds_iff_numbered s (reduct h model)).symm)

def corridor (h : P ⟶ Q) : room P ⟶ room Q :=
  ⟨(RuntimeRoom.corridor h).sen, (RuntimeRoom.corridor h).mod, fun m s => holds_map h s m.as⟩

theorem corridor_id (P : EntrySignature) : corridor (𝟙 P) = 𝟙 (room P) :=
  Room.hom_ext
    (congrArg (fun f : RuntimeRoom.room P ⟶ RuntimeRoom.room P => f.sen) (RuntimeRoom.corridor_id P))
    (congrArg (fun f : RuntimeRoom.room P ⟶ RuntimeRoom.room P => f.mod) (RuntimeRoom.corridor_id P))

theorem corridor_comp (h : P ⟶ Q) (k : Q ⟶ R) : corridor (h ≫ k) = corridor h ≫ corridor k :=
  Room.hom_ext
    (congrArg (fun f : RuntimeRoom.room P ⟶ RuntimeRoom.room R => f.sen) (RuntimeRoom.corridor_comp h k))
    (congrArg (fun f : RuntimeRoom.room P ⟶ RuntimeRoom.room R => f.mod) (RuntimeRoom.corridor_comp h k))

def inst : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨room, corridor, corridor_id, corridor_comp⟩

def comparisonCorridor (P : EntrySignature) : RuntimeRoom.room P ⟶ room P :=
  ⟨id, 𝟭 _, fun m s => holds_iff_numbered s m.as⟩

theorem comparison_natural (h : P ⟶ Q) :
    RuntimeRoom.corridor h ≫ comparisonCorridor Q = comparisonCorridor P ≫ corridor h :=
  Room.hom_ext rfl (Discrete.functor_ext fun _ => rfl)

/-- Interpret the same generated sentence by actual coloured completion. -/
def comparison : Inst.CoHom RuntimeRoom.inst inst where
  Φ := 𝟭 _
  ρ := { app := comparisonCorridor
         naturality := fun {P Q} h => comparison_natural (P := P) (Q := Q) h }

/-- Global numbered satisfaction after re-emission ranges over the
pulled-back target valuations at the canonical cell count. -/
theorem numbered_satisfaction_map (h : P ⟶ Q) (s : RuntimeRoom.Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (s.map h).numbered ↔
      ∀ input : Tuple (Val cells) Q.args, Holds s (reduct h ⟨cells, input⟩) :=
  (s.numbered_satisfaction_map h cells).trans
    (forall_congr' fun input => (holds_iff_numbered s (reduct h ⟨cells, input⟩)).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom
