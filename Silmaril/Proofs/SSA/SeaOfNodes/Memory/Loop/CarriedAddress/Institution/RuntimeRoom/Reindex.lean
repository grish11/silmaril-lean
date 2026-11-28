module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Proofs

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

theorem modelEntry_reindex (h : P ⟶ Q) (model : EntryModel Q) (heap : Heap model.cells) :
    RuntimeEntry.reindex h (modelEntry model heap).val = (modelEntry (reduct h model) heap).val :=
  RuntimeEntry.reindex_encode h ⟨model.input, heap⟩

theorem observe_map (h : P ⟶ Q) (program : GeneratedProgram P.args)
    (model : EntryModel Q) (heap : Heap model.cells) :
    RuntimeEntry.observeProgram (program.map h).program (modelEntry model heap).val =
      RuntimeEntry.observeProgram program.program (modelEntry (reduct h model) heap).val := by
  obtain ⟨graph, _, rfl⟩ := program
  let raw := modelEntry model heap
  have observed := RuntimeEntry.observe_mapGraph h graph raw.val raw.property
  rw [modelEntry_reindex h model heap] at observed
  exact observed

theorem satisfaction_map (h : P ⟶ Q) (e : Sentence P) (model : EntryModel Q) :
    (e.map h).Holds model ↔ e.Holds (reduct h model) := by
  simp only [Sentence.Holds, Sentence.map, observe_map]
  rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Proofs
