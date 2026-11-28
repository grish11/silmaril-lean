module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Regression
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom

open CategoryTheory
open Silmaril.Logic.Institution (Inst)
open Fixture
open Silmaril.MLIR.MemRef (Buffer)
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

private def reversed : Graph args := mapGraph swapPorts graph
private def equation : Equation scope := ⟨graph, reversed⟩

private def distinctModel : EntryModel scope := ⟨3, input 1⟩
private def swappedModel : EntryModel scope :=
  ⟨3, .cons (1 : Address 3) (.cons (0 : Address 3) (.cons (9 : Word) (.cons (0 : Word) .nil)))⟩

private theorem switched :
    (lowerEquation equation).lhs.observe distinctModel ⟨initial 7⟩ =
      Part.some (0, Buffer.mk afterFeedback) :=
  (GeneratedProgram.observe_eq_some_iff _ _ _ _).mpr ⟨1, by
    change MemRef.run graph (input 1) 1 ⟨initial 7⟩ = some (0, Buffer.mk afterFeedback)
    rw [MemRef.run_eq_evalWithin]
    rfl⟩

example :
    ((lowerEquation equation).map swapPorts).lhs.observe swappedModel ⟨initial 7⟩ =
      Part.some (0, Buffer.mk afterFeedback) :=
  (GeneratedProgram.observe_map swapPorts (lowerEquation equation).lhs swappedModel ⟨initial 7⟩).trans switched

private theorem rejected : ¬ (lowerEquation equation).Holds distinctModel := by
  intro holds
  have reversedReturn : (lowerEquation equation).rhs.observe distinctModel ⟨initial 7⟩ =
      Part.some (0, Buffer.mk ((initial 7).write 1 9)) :=
    (GeneratedProgram.observe_eq_some_iff _ _ _ _).mpr ⟨0, by
      change MemRef.run reversed (input 1) 0 ⟨initial 7⟩ = some (0, Buffer.mk ((initial 7).write 1 9))
      rw [MemRef.run_eq_evalWithin]
      rfl⟩
  have same := holds ⟨initial 7⟩
  rw [switched, reversedReturn] at same
  have first := congrArg (fun result : Word × Buffer 3 => result.2.cell 0) (Part.some_inj.mp same)
  exact (by decide : (9 : Word) ≠ 7) first

-- Satisfaction for a nonidentity signature corridor, then the native
-- and runtime comorphism conditions on the same re-emitted equation.
example :
    ¬ (room scope).Sat (Discrete.mk swappedModel)
      ((corridor swapPorts).sen (lowerEquation equation)) := by
  intro holds
  exact rejected ((corridor swapPorts).sat (Discrete.mk swappedModel) _ |>.mp holds)

example :
    ¬ (room scope).Sat (Discrete.mk swappedModel)
      ((comparison.ρ.app scope).sen (equation.map swapPorts)) := by
  intro holds
  have native := (Inst.CoHom.satisfaction comparison scope (Discrete.mk swappedModel)
    (equation.map swapPorts)).mp holds
  exact rejected ((satisfaction equation distinctModel).mpr ((equation.satisfaction swapPorts swappedModel).mp native))

example :
    ¬ (RuntimeRoom.room scope).Sat (Discrete.mk swappedModel)
      ((RuntimeRoom.lowerEquation equation).map swapPorts) := by
  intro holds
  have emitted := (Inst.CoHom.satisfaction runtimeComparison scope (Discrete.mk swappedModel)
    ((RuntimeRoom.lowerEquation equation).map swapPorts)).mpr holds
  exact rejected ((Sentence.satisfaction_map swapPorts _ swappedModel).mp emitted)

-- Identification can erase the distinction. Global target truth covers
-- the reduct image, which contains only coincident address valuations.
example : ∀ input : RVSDG.Tuple (Val 3) scope.args,
    (lowerEquation (equation.map identifyPorts)).Holds (⟨3, input⟩ : EntryModel scope) := by
  have same : mapGraph identifyPorts equation.lhs = mapGraph identifyPorts equation.rhs := by
    change mapGraph identifyPorts graph = mapGraph identifyPorts (mapGraph swapPorts graph)
    rw [← Institution.mapGraph_comp]
    rfl
  intro input initial
  exact congrArg (fun g => (GeneratedProgram.lower g).observe ⟨3, input⟩ initial) same

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.MemRefRoom
