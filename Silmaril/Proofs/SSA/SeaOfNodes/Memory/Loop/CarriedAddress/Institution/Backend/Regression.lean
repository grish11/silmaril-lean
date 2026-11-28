module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend

open CategoryTheory
open RVSDG (Tuple)
open Fixture
open Memory.Diamond.Institution (reduct pullInput_get)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

private abbrev scope : EntrySignature := ⟨args⟩

private def swapPorts : scope ⟶ scope :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail p) => .tail (.tail p)⟩

private def identifyPorts : scope ⟶ scope :=
  ⟨fun
    | .head => .head
    | .tail .head => .head
    | .tail (.tail p) => .tail (.tail p)⟩

private def equation : Equation scope := ⟨graph, mapGraph swapPorts graph⟩
private def distinctModel : EntryModel scope := ⟨3, input 1⟩
private def swappedModel : EntryModel scope :=
  ⟨3, .cons (1 : Address 3) (.cons (0 : Address 3) (.cons (9 : Word) (.cons (0 : Word) .nil)))⟩

private theorem switched :
    rvsdg.observe (rvsdg.emit equation) .lhs distinctModel (Fixture.initial 7) =
      Part.some (rvsdg.result 3 (0, afterFeedback)) :=
  (rvsdg.correct equation .lhs distinctModel (Fixture.initial 7) (0, afterFeedback)).mpr ⟨1, rfl⟩

-- Translate after a nonidentity swap, then decode the actual MemRef result.
example :
    (memref.observe (rvsdg.translate memref (rvsdg.reemit swapPorts (rvsdg.emit equation)))
      .lhs swappedModel (memref.initial 3 (Fixture.initial 7))).map (memref.result 3).symm =
      Part.some (0, afterFeedback) := by
  have emitted := rvsdg.observe_translate_reemit memref swapPorts (rvsdg.emit equation)
    .lhs swappedModel (Fixture.initial 7)
  exact emitted.trans ((congrArg (Part.map (rvsdg.result 3).symm) switched).trans
    ((Part.map_some (rvsdg.result 3).symm _).trans
      (congrArg Part.some ((rvsdg.result 3).symm_apply_apply (0, afterFeedback)))))

private theorem identified : ∀ targetInput : Tuple (Val 3) scope.args,
    rvsdg.Holds (rvsdg.reemit identifyPorts (rvsdg.emit equation)) (⟨3, targetInput⟩ : EntryModel scope) := by
  have same : (equation.map identifyPorts).lhs = (equation.map identifyPorts).rhs := by
    change mapGraph identifyPorts graph = mapGraph identifyPorts (mapGraph swapPorts graph)
    rw [← Institution.mapGraph_comp]
    rfl
  intro targetInput
  apply (rvsdg.holds_iff_source _ _).mpr
  change (equation.map identifyPorts).Holds _
  intro heap word final
  change nativeReturns (equation.map identifyPorts).lhs _ heap word final ↔
    nativeReturns (equation.map identifyPorts).rhs _ heap word final
  rw [same]

example : ∀ model : EntryModel scope, InReductImage identifyPorts 3 model →
    memref.Holds (rvsdg.translate memref (rvsdg.emit equation)) model := by
  intro model inImage
  exact (rvsdg.holds_translate memref _ _).mpr
    ((rvsdg.holds_reemit_iff_image identifyPorts _ 3).mp identified model inImage)

example : ¬ memref.Holds (rvsdg.translate memref (rvsdg.emit equation)) distinctModel := by
  intro holds
  have agrees := (rvsdg.holds_translate memref _ _).mp holds
  have reversed := (rvsdg.correct equation .rhs distinctModel (Fixture.initial 7)
    (0, (Fixture.initial 7).write 1 9)).mpr ⟨0, rfl⟩
  have same := agrees (Fixture.initial 7)
  have equal := (rvsdg.result 3).injective (Part.some_inj.mp (switched.symm.trans (same.trans reversed)))
  exact (by decide : (9 : Word) ≠ 7) (congrFun (congrArg Prod.snd equal) (0 : Address 3))

-- The distinct valuation is excluded by the identifying reduct.
example : ¬ InReductImage identifyPorts 3 distinctModel := by
  rintro ⟨targetInput, equal⟩
  let head (model : EntryModel scope) := model.input.get .head |>.val
  let second (model : EntryModel scope) := model.input.get (.tail .head) |>.val
  have first := congrArg head equal
  have next := congrArg second equal
  have pulled :
      head (reduct identifyPorts ⟨3, targetInput⟩) = second (reduct identifyPorts ⟨3, targetInput⟩) := by
    change ((reduct identifyPorts ⟨3, targetInput⟩).input.get .head).val =
      ((reduct identifyPorts ⟨3, targetInput⟩).input.get (.tail .head)).val
    simp only [reduct, pullInput_get]
    rfl
  exact (by decide : (0 : Nat) ≠ 1) (first.symm.trans (pulled.trans next))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend
