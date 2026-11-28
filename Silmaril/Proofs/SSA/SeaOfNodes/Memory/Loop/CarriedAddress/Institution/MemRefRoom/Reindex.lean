module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Observation

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Proofs

open CategoryTheory
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

theorem map_id (e : Sentence P) : e.map (𝟙 P) = e := by
  obtain ⟨⟨left, _, rfl⟩, ⟨right, _, rfl⟩⟩ := e
  simp only [Sentence.map, GeneratedProgram.map, Institution.mapGraph_id]
  rfl

theorem map_comp (h : P ⟶ Q) (k : Q ⟶ R) (e : Sentence P) :
    e.map (h ≫ k) = (e.map h).map k := by
  simp only [Sentence.map, GeneratedProgram.map, Institution.mapGraph_comp]
  rfl

theorem satisfaction_map (h : P ⟶ Q) (e : Sentence P) (model : EntryModel Q) :
    (e.map h).Holds model ↔ e.Holds (reduct h model) := by
  simp only [Sentence.Holds, Sentence.map, observe_map]
  rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Proofs
