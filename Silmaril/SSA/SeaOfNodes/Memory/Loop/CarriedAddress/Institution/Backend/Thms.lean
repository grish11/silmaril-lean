module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Observation

/-! Common observation, re-emission and corridor laws for the generated backends. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Tuple)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

theorem observe_eq_some_iff (backend : Backend) (s : backend.Sentence P) (side : Side)
    (model : EntryModel P) (heap : Heap model.cells) (value : Word × Heap model.cells) :
    backend.observe s side model (backend.initial model.cells heap) =
      Part.some (backend.result model.cells value) ↔
      nativeReturns ((backend.source s).graph side) model heap value.1 value.2 :=
  Proofs.observe_eq_some_iff backend s side model heap value

theorem observe_eq_none_iff (backend : Backend) (s : backend.Sentence P) (side : Side)
    (model : EntryModel P) (heap : Heap model.cells) :
    backend.observe s side model (backend.initial model.cells heap) = Part.none ↔
      (nativeReturns ((backend.source s).graph side) model).NoReturn heap :=
  Proofs.observe_eq_none_iff backend s side model heap

theorem observe_reemit (backend : Backend) (h : P ⟶ Q) (s : backend.Sentence P) (side : Side)
    (model : EntryModel Q) (initial : backend.Initial model.cells) :
    backend.observe (backend.reemit h s) side model initial =
      backend.observe s side (reduct h model) initial :=
  Proofs.observe_reemit backend h s side model initial

/-- The actual partial observations agree after decoding each result.
Each backend supplies its own finite witnesses. -/
theorem observe_translate (sender receiver : Backend) (s : sender.Sentence P) (side : Side)
    (model : EntryModel P) (heap : Heap model.cells) :
    (receiver.observe (sender.translate receiver s) side model (receiver.initial model.cells heap)).map
      (receiver.result model.cells).symm =
      (sender.observe s side model (sender.initial model.cells heap)).map (sender.result model.cells).symm :=
  Proofs.observe_translate sender receiver s side model heap

/-- Translate a re-emitted equation and compare the decoded observation
with the original observer at the pulled-back valuation. -/
theorem observe_translate_reemit (sender receiver : Backend) (h : P ⟶ Q) (s : sender.Sentence P)
    (side : Side) (model : EntryModel Q) (heap : Heap model.cells) :
    (receiver.observe (sender.translate receiver (sender.reemit h s)) side model
      (receiver.initial model.cells heap)).map (receiver.result model.cells).symm =
      (sender.observe s side (reduct h model) (sender.initial model.cells heap)).map
        (sender.result model.cells).symm :=
  (sender.observe_translate receiver (sender.reemit h s) side model heap).trans
    (congrArg (Part.map (sender.result model.cells).symm)
      (sender.observe_reemit h s side model (sender.initial model.cells heap)))

theorem holds_iff_source (backend : Backend) (s : backend.Sentence P) (model : EntryModel P) :
    backend.Holds s model ↔ (backend.source s).Holds model :=
  Proofs.holds_iff_source backend s model

theorem holds_reemit (backend : Backend) (h : P ⟶ Q) (s : backend.Sentence P) (model : EntryModel Q) :
    backend.Holds (backend.reemit h s) model ↔ backend.Holds s (reduct h model) :=
  Proofs.holds_reemit backend h s model

theorem holds_reemit_iff_image (backend : Backend) (h : P ⟶ Q) (s : backend.Sentence P) (cells : Nat) :
    (∀ input : Tuple (Val cells) Q.args, backend.Holds (backend.reemit h s) (⟨cells, input⟩ : EntryModel Q)) ↔
      ∀ model : EntryModel P, InReductImage h cells model → backend.Holds s model :=
  Proofs.holds_reemit_iff_image backend h s cells

theorem holds_translate (sender receiver : Backend) (s : sender.Sentence P) (model : EntryModel P) :
    receiver.Holds (sender.translate receiver s) model ↔ sender.Holds s model := by
  rw [holds_iff_source, holds_iff_source, translate, receiver.source_emit]

@[simp] theorem reemit_id (backend : Backend) (s : backend.Sentence P) : backend.reemit (𝟙 P) s = s := by
  rw [reemit, Equation.map_id, backend.emit_source]

theorem reemit_comp (backend : Backend) (h : P ⟶ Q) (k : Q ⟶ R) (s : backend.Sentence P) :
    backend.reemit (h ≫ k) s = backend.reemit k (backend.reemit h s) := by
  simp only [reemit, backend.source_emit, Equation.map_comp]

theorem translate_reemit (sender receiver : Backend) (h : P ⟶ Q) (s : sender.Sentence P) :
    sender.translate receiver (sender.reemit h s) = receiver.reemit h (sender.translate receiver s) := by
  simp only [translate, reemit, sender.source_emit, receiver.source_emit]

def corridor (backend : Backend) (h : P ⟶ Q) : backend.room P ⟶ backend.room Q :=
  ⟨backend.reemit h, (Institution.corridor h).mod, fun m s => backend.holds_reemit h s m.as⟩

theorem corridor_id (backend : Backend) (P : EntrySignature) : backend.corridor (𝟙 P) = 𝟙 (backend.room P) :=
  Room.hom_ext (funext backend.reemit_id)
    (congrArg (fun f : Institution.room P ⟶ Institution.room P => f.mod) (Institution.corridor_id P))

theorem corridor_comp (backend : Backend) (h : P ⟶ Q) (k : Q ⟶ R) :
    backend.corridor (h ≫ k) = backend.corridor h ≫ backend.corridor k :=
  Room.hom_ext (funext (backend.reemit_comp h k))
    (congrArg (fun f : Institution.room P ⟶ Institution.room R => f.mod) (Institution.corridor_comp h k))

def inst (backend : Backend) : Inst.{0, 0, 0, 0, 0} where
  Sign := EntrySignature
  I := ⟨backend.room, backend.corridor, backend.corridor_id, backend.corridor_comp⟩

def comparisonCorridor (backend : Backend) (P : EntrySignature) : Institution.room P ⟶ backend.room P :=
  ⟨backend.emit, 𝟭 _, fun m e =>
    (backend.holds_iff_source (backend.emit e) m.as).trans
      (iff_of_eq (congrArg (fun equation : Equation P => equation.Holds m.as) (backend.source_emit e)))⟩

theorem comparison_natural (backend : Backend) (h : P ⟶ Q) :
    Institution.corridor h ≫ backend.comparisonCorridor Q =
      backend.comparisonCorridor P ≫ backend.corridor h :=
  Room.hom_ext (funext fun e =>
    congrArg (fun equation : Equation P => backend.emit (equation.map h)) (backend.source_emit e).symm)
    (Discrete.functor_ext fun _ => rfl)

def comparison (backend : Backend) : Inst.CoHom Institution.inst backend.inst where
  Φ := 𝟭 _
  ρ := { app := backend.comparisonCorridor
         naturality := fun {P Q} h => backend.comparison_natural (P := P) (Q := Q) h }

def translateCorridor (sender receiver : Backend) (P : EntrySignature) : sender.room P ⟶ receiver.room P :=
  ⟨sender.translate receiver, 𝟭 _, fun m s => sender.holds_translate receiver s m.as⟩

def comparisonBetween (sender receiver : Backend) : Inst.CoHom sender.inst receiver.inst where
  Φ := 𝟭 _
  ρ := { app := sender.translateCorridor receiver
         naturality := fun {P Q} h => Room.hom_ext (funext (sender.translate_reemit receiver (P := P) (Q := Q) h))
           (Discrete.functor_ext fun _ => rfl) }

theorem translateCorridor_id (backend : Backend) (P : EntrySignature) :
    backend.translateCorridor backend P = 𝟙 (backend.room P) :=
  Room.hom_ext (funext backend.emit_source) rfl

theorem translateCorridor_comp (sender middle receiver : Backend) (P : EntrySignature) :
    sender.translateCorridor middle P ≫ middle.translateCorridor receiver P =
      sender.translateCorridor receiver P :=
  Room.hom_ext (funext fun s => congrArg (receiver.emit (P := P)) (middle.source_emit (sender.source s)))
    (Discrete.functor_ext fun _ => rfl)

theorem comparisonCorridor_factors (sender receiver : Backend) (P : EntrySignature) :
    sender.comparisonCorridor P ≫ sender.translateCorridor receiver P = receiver.comparisonCorridor P :=
  Room.hom_ext (funext fun e => congrArg (receiver.emit (P := P)) (sender.source_emit e))
    (Discrete.functor_ext fun _ => rfl)

theorem comparisonBetween_comp (sender middle receiver : Backend) :
    Inst.CoHom.comp (sender.comparisonBetween middle) (middle.comparisonBetween receiver) =
      sender.comparisonBetween receiver :=
  Inst.CoHom.ext rfl (NatTrans.ext (funext (translateCorridor_comp sender middle receiver)))

theorem comparison_factors (sender receiver : Backend) :
    Inst.CoHom.comp sender.comparison (sender.comparisonBetween receiver) = receiver.comparison :=
  Inst.CoHom.ext rfl (NatTrans.ext (funext (comparisonCorridor_factors sender receiver)))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend
