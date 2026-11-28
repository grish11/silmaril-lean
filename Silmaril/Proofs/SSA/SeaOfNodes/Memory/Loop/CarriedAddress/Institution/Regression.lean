module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution

open CategoryTheory
open SeaOfNodes.Loop (Incoming)
open Fixture
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

private abbrev scope : EntrySignature := ⟨args⟩
private def model (second : Address 3) : EntryModel scope := ⟨3, input second⟩

private theorem switched : nativeReturns graph (model 1) (initial 7) 0 afterFeedback :=
  ⟨1, rfl⟩

example : petriReturns graph (model 1) (initial 7) 0 afterFeedback ∧
    memrefReturns graph (model 1) (initial 7) 0 afterFeedback ∧
    runtimeObserve graph (model 1) (initial 7) = Part.some (encodeResult 0 afterFeedback) :=
  ⟨(petriReturns_iff_native _ _ _ _ _).mpr switched, (memrefReturns_iff_native _ _ _ _ _).mpr switched,
    (runtimeObserve_eq_some_iff_native _ _ _ _ _).mpr switched⟩

-- Immediate exit still executes the first store. All three cells are observed.
example : petriReturns graph (model 1) (initial 0) 0 ((initial 0).write 0 9) ∧
    memrefReturns graph (model 1) (initial 0) 0 ((initial 0).write 0 9) :=
  ⟨(petriReturns_iff_native _ _ _ _ _).mpr ⟨0, rfl⟩,
    (memrefReturns_iff_native _ _ _ _ _).mpr ⟨0, rfl⟩⟩

private def swapPorts : scope ⟶ scope :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail p) => .tail (.tail p)⟩

private def reversed : Graph args := mapGraph swapPorts graph
private def equation : Equation scope := ⟨graph, reversed⟩
private def reversedFinal : Heap 3 := (initial 7).write 1 9

private theorem reversed_exit (budget : Nat) :
    reversed.evalWithin (input 1) budget .entry (initial 7) = some (0, reversedFinal) := by
  cases budget <;> rfl

-- Reversing the arrival operands at the same valuation still returns
-- zero, but exits from its first activation and leaves cell 0 at seven.
private theorem rejected : ¬ equation.Holds (model 1) := by
  intro holds
  obtain ⟨budget, returned⟩ := (holds (initial 7) 0 afterFeedback).mp switched
  change reversed.evalWithin (input 1) budget .entry (initial 7) = some (0, afterFeedback) at returned
  rw [reversed_exit] at returned
  have first := congrFun (congrArg Prod.snd (Option.some.inj returned)) 0
  exact (by decide : (7 : Word) ≠ 9) first

example : ¬ petriHolds equation (model 1) ∧ ¬ memrefHolds equation (model 1) :=
  ⟨fun holds => rejected ((petri_satisfaction _ _).mp holds),
    fun holds => rejected ((memref_satisfaction _ _).mp holds)⟩

private theorem alias_step (arrival : Incoming) (heap : Heap 3) :
    graph.step (input 0) arrival heap = reversed.step (input 0) arrival heap := by
  cases arrival <;> rfl

private theorem alias_eval (budget : Nat) (arrival : Incoming) (heap : Heap 3) :
    graph.evalWithin (input 0) budget arrival heap =
      reversed.evalWithin (input 0) budget arrival heap := by
  induction budget generalizing arrival heap with
  | zero =>
    simp only [Graph.evalWithin, alias_step]
  | succ budget ih =>
    simp only [Graph.evalWithin, alias_step]
    cases reversed.step (input 0) arrival heap with
    | inl _ => rfl
    | inr next => exact ih .backedge next

-- The two syntaxes agree at the aliasing valuation for every initial heap.
example : petriHolds equation (model 0) ∧ memrefHolds equation (model 0) := by
  have holds : equation.Holds (model 0) := by
    intro heap word final
    exact exists_congr fun budget => by
      change graph.evalWithin (input 0) budget .entry heap = some (word, final) ↔
        reversed.evalWithin (input 0) budget .entry heap = some (word, final)
      rw [alias_eval budget .entry heap]
  exact ⟨(petri_satisfaction _ _).mpr holds, (memref_satisfaction _ _).mpr holds⟩

private def swappedModel : EntryModel scope := ⟨3,
  .cons (1 : Address 3) (.cons (0 : Address 3) (.cons (9 : Word) (.cons (0 : Word) .nil)))⟩

-- Applying the same typed swap to the equation and its valuation
-- transports the rejected equation with both Phi columns intact.
example : ¬ memrefHolds (equation.map swapPorts) swappedModel := by
  intro holds
  have pulled := (memref_satisfaction_reindex swapPorts equation swappedModel).mp holds
  exact rejected ((memref_satisfaction equation (reduct swapPorts swappedModel)).mp pulled)

example : petriReturns (mapGraph swapPorts graph) swappedModel (initial 7) 0 afterFeedback :=
  (petriReturns_iff_native _ _ _ _ _).mpr ((nativeReturns_mapGraph _ _ _ _ _ _).mpr switched)

private theorem repeated_heap :
    graph.step (input 0) .backedge afterEntry = .inr afterEntry := by
  change Sum.inr (afterEntry.write 0 9) = Sum.inr afterEntry
  apply congrArg Sum.inr
  funext cell
  by_cases selected : cell = 0
  · subst cell
    simp [Heap.write, afterEntry]
  · simp [Heap.write, selected]

private theorem feedback_never_exits (budget : Nat) :
    graph.evalWithin (input 0) budget .backedge afterEntry = none := by
  induction budget with
  | zero => simp only [Graph.evalWithin, repeated_heap, Sum.elim_inr]
  | succ budget ih => simpa only [Graph.evalWithin, repeated_heap, Sum.elim_inr] using ih

-- At this initialized heap, aliasing the two ports overwrites the only
-- selected cell with nine, then keeps taking the same feedback edge.
private theorem absent : (nativeReturns graph (model 0)).NoReturn (initial 7) := by
  intro word final
  rintro ⟨budget, returned⟩
  cases budget with
  | zero => cases returned
  | succ budget =>
    change graph.evalWithin (input 0) budget .backedge afterEntry = some (word, final) at returned
    rw [feedback_never_exits] at returned
    cases returned

example : (petriReturns graph (model 0)).NoReturn (initial 7) ∧
    (memrefReturns graph (model 0)).NoReturn (initial 7) ∧
    runtimeObserve graph (model 0) (initial 7) = Part.none :=
  ⟨(petri_no_return_iff_native _ _ _).mpr absent, (memref_no_return_iff_native _ _ _).mpr absent,
    (runtime_no_return_iff_native _ _ _).mpr absent⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution
