module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom

open CategoryTheory
open Silmaril.Logic.Institution (Inst)
open Fixture
open SeaOfNodes.Loop (Incoming)
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

private theorem switch_observed :
    RuntimeEntry.observe graph (modelEntry distinctModel (initial 7)).val =
      Part.some (encodeResult 0 afterFeedback) :=
  (RuntimeEntry.observe_eq_some_iff_native graph (RuntimeEntry.decode_encode _)
    0 afterFeedback).mpr ⟨1, rfl⟩

-- A nonidentity map sends the emitted program forward and the model back.
example : RuntimeEntry.observeProgram ((lowerEquation equation).map swapPorts).lhs.program
    (modelEntry swappedModel (initial 7)).val = Part.some (encodeResult 0 afterFeedback) :=
  (GeneratedProgram.observe_map swapPorts (lowerEquation equation).lhs swappedModel (initial 7)).trans
    switch_observed

private theorem runtime_rejected : ¬ (lowerEquation equation).Holds distinctModel := by
  intro holds
  have reversedReturn : RuntimeEntry.observe reversed (modelEntry distinctModel (initial 7)).val =
      Part.some (encodeResult 0 ((initial 7).write 1 9)) :=
    (RuntimeEntry.observe_eq_some_iff_native reversed (RuntimeEntry.decode_encode _)
      0 ((initial 7).write 1 9)).mpr ⟨0, rfl⟩
  have equal : RuntimeEntry.observe graph (modelEntry distinctModel (initial 7)).val =
      RuntimeEntry.observe reversed (modelEntry distinctModel (initial 7)).val := holds (initial 7)
  rw [switch_observed, reversedReturn] at equal
  have cellZero := congrArg (fun output => (output.get (.tail .head)) (0 : Address 3))
    (Part.some_inj.mp equal)
  exact (by decide : (9 : Word) ≠ 7) cellZero

-- Exercise the bundled comparison at a renamed sentence and model.
example : ¬ (room scope).Sat (Discrete.mk swappedModel)
    ((comparison.ρ.app scope).sen (equation.map swapPorts)) := by
  intro holds
  have native := (Inst.CoHom.satisfaction comparison scope (Discrete.mk swappedModel)
    (equation.map swapPorts)).mp holds
  have pulled := (equation.satisfaction swapPorts swappedModel).mp native
  exact runtime_rejected ((satisfaction equation distinctModel).mpr pulled)

-- Identifying the two address ports makes the two re-emitted graphs
-- equal. The resulting global truth cannot cover distinct source addresses.
example : RuntimeEntry.Holds (equation.map identifyPorts) 3 := by
  have same : mapGraph identifyPorts equation.lhs = mapGraph identifyPorts equation.rhs := by
    change mapGraph identifyPorts graph = mapGraph identifyPorts (mapGraph swapPorts graph)
    rw [← Institution.mapGraph_comp]
    rfl
  intro raw _
  exact congrArg (fun graph => RuntimeEntry.observe graph raw) same

example : ¬ RuntimeEntry.Holds equation 3 := by
  intro holds
  exact runtime_rejected ((holds_iff_all_models equation 3).mp holds (input 1))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeRoom
