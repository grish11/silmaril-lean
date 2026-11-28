module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Proofs

open CategoryTheory
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

set_option backward.isDefEq.respectTransparency false

variable {P Q : EntrySignature}

theorem observe_eq_some_iff (backend : Backend) (s : backend.Sentence P) (side : Side)
    (model : EntryModel P) (heap : Heap model.cells) (value : Word × Heap model.cells) :
    backend.observe s side model (backend.initial model.cells heap) =
      Part.some (backend.result model.cells value) ↔
      nativeReturns ((backend.source s).graph side) model heap value.1 value.2 :=
  calc
    _ = _ ↔ backend.observe (backend.emit (backend.source s)) side model (backend.initial model.cells heap) =
      Part.some (backend.result model.cells value) := by rw [backend.emit_source]
    _ ↔ _ := backend.correct (backend.source s) side model heap value

theorem observe_eq_none_iff (backend : Backend) (s : backend.Sentence P) (side : Side)
    (model : EntryModel P) (heap : Heap model.cells) :
    backend.observe s side model (backend.initial model.cells heap) = Part.none ↔
      (nativeReturns ((backend.source s).graph side) model).NoReturn heap := by
  rw [Part.eq_none_iff]
  constructor
  · intro absent word final returned
    exact absent _ (Part.eq_some_iff.mp ((observe_eq_some_iff backend s side model heap (word, final)).mpr returned))
  · intro absent result returned
    obtain ⟨⟨word, final⟩, rfl⟩ := (backend.result model.cells).surjective result
    exact absent word final ((observe_eq_some_iff backend s side model heap (word, final)).mp
      (Part.eq_some_iff.mpr returned))

theorem observe_reemit (backend : Backend) (h : P ⟶ Q) (s : backend.Sentence P) (side : Side)
    (model : EntryModel Q) (initial : backend.Initial model.cells) :
    backend.observe (backend.reemit h s) side model initial =
      backend.observe s side (reduct h model) initial := by
  obtain ⟨heap, rfl⟩ := (backend.initial model.cells).surjective initial
  apply Part.ext
  intro output
  obtain ⟨value, rfl⟩ := (backend.result model.cells).surjective output
  have related : nativeReturns ((backend.source (backend.reemit h s)).graph side) model heap value.1 value.2 ↔
      nativeReturns ((backend.source s).graph side) (reduct h model) heap value.1 value.2 := by
    rw [show backend.source (backend.reemit h s) = (backend.source s).map h from backend.source_emit _]
    cases side <;> exact nativeReturns_mapGraph h _ model heap value.1 value.2
  exact (Part.eq_some_iff.symm.trans (observe_eq_some_iff backend _ side model heap value)).trans
    (related.trans ((observe_eq_some_iff backend s side (reduct h model) heap value).symm.trans Part.eq_some_iff))

theorem observe_translate (sender receiver : Backend) (s : sender.Sentence P) (side : Side)
    (model : EntryModel P) (heap : Heap model.cells) :
    (receiver.observe (sender.translate receiver s) side model (receiver.initial model.cells heap)).map
      (receiver.result model.cells).symm =
      (sender.observe s side model (sender.initial model.cells heap)).map (sender.result model.cells).symm := by
  have member (backend : Backend) (sentence : backend.Sentence P) (value : Word × Heap model.cells) :
      value ∈ (backend.observe sentence side model (backend.initial model.cells heap)).map
        (backend.result model.cells).symm ↔
        nativeReturns ((backend.source sentence).graph side) model heap value.1 value.2 := by
    rw [Part.mem_map_iff]
    constructor
    · rintro ⟨observed, found, equal⟩
      have encoded : observed = backend.result model.cells value :=
        ((backend.result model.cells).symm_apply_eq).mp equal
      exact (observe_eq_some_iff backend sentence side model heap value).mp
        (Part.eq_some_iff.mpr (encoded ▸ found))
    · intro returned
      exact ⟨_, Part.eq_some_iff.mp ((observe_eq_some_iff backend sentence side model heap value).mpr returned),
        (backend.result model.cells).symm_apply_apply value⟩
  apply Part.ext
  intro value
  rw [member, member, translate, receiver.source_emit]

theorem holds_iff_source (backend : Backend) (s : backend.Sentence P) (model : EntryModel P) :
    backend.Holds s model ↔ (backend.source s).Holds model := by
  constructor
  · intro holds heap word final
    have same := iff_of_eq (congrArg (· = Part.some (backend.result model.cells (word, final)))
      (holds (backend.initial model.cells heap)))
    exact (observe_eq_some_iff backend s .lhs model heap (word, final)).symm.trans
      (same.trans (observe_eq_some_iff backend s .rhs model heap (word, final)))
  · intro holds initial
    obtain ⟨heap, rfl⟩ := (backend.initial model.cells).surjective initial
    apply Part.ext
    intro result
    obtain ⟨⟨word, final⟩, rfl⟩ := (backend.result model.cells).surjective result
    rw [← Part.eq_some_iff, ← Part.eq_some_iff, observe_eq_some_iff, observe_eq_some_iff]
    exact holds heap word final

theorem holds_reemit (backend : Backend) (h : P ⟶ Q) (s : backend.Sentence P) (model : EntryModel Q) :
    backend.Holds (backend.reemit h s) model ↔ backend.Holds s (reduct h model) := by
  refine forall_congr' fun initial => ?_
  rw [observe_reemit, observe_reemit]

theorem holds_reemit_iff_image (backend : Backend) (h : P ⟶ Q) (s : backend.Sentence P) (cells : Nat) :
    (∀ input : Tuple (Val cells) Q.args, backend.Holds (backend.reemit h s) (⟨cells, input⟩ : EntryModel Q)) ↔
      ∀ model : EntryModel P, InReductImage h cells model → backend.Holds s model := by
  constructor
  · rintro holds model ⟨input, rfl⟩
    exact (holds_reemit backend h s _).mp (holds input)
  · intro holds input
    exact (holds_reemit backend h s _).mpr (holds _ ⟨input, rfl⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Proofs
