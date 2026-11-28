module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CategoryTheory
open Fixture
open RVSDG (Origin Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution renaming Model → EntryModel

private def model (second : Address 4) : EntryModel captures := ⟨4, input second⟩

private theorem observes (second : Address 4) (fuel : Nat) (heap : Heap 4)
    (result : MemRef.runFuel graph (input second) fuel ⟨initial⟩ = some (0, ⟨heap⟩)) :
    runtimeObserve graph (model second) initial = Part.some (encodeResult 0 heap) ∧
      petriReturns graph (model second) initial 0 heap := by
  have native := (memrefReturns_iff_native graph (model second) initial 0 heap).mp ⟨fuel, result⟩
  exact ⟨(runtimeObserve_eq_some_iff_native graph (model second) initial 0 heap).mpr native,
    (petriReturns_iff_native graph (model second) initial 0 heap).mpr native⟩

-- Both layouts go through the same observation adapters and retain every cell.
example : runtimeObserve graph (model 1) initial = Part.some (encodeResult 0 final) ∧
    petriReturns graph (model 1) initial 0 final :=
  observes 1 5 final ((MemRef.run_eq_evalWithin graph (input 1) 2 initial).trans rfl)

example : runtimeObserve graph (model 0) initial = Part.some (encodeResult 0 aliased) ∧
    petriReturns graph (model 0) initial 0 aliased :=
  observes 0 4 aliased ((MemRef.run_eq_evalWithin graph (input 0) 1 initial).trans rfl)

private def stationary : Graph args := { graph with feedbackFirst := .head, feedbackSecond := .tail .head }

private def comparison : Sentence captures := .equation graph stationary

private theorem coincident_eval (input : Tuple (Val 4) args) (budget : Nat) (header : Header 4)
    (same : header.first = header.second) :
    graph.evalWithin input budget header = stationary.evalWithin input budget header := by
  have feedback (h : Header 4) (equal : h.first = h.second) :
      graph.feedback input h = stationary.feedback input h := by
    funext heap
    change Header.mk h.second h.first heap = Header.mk h.first h.second heap
    rw [equal]
  induction budget generalizing header with
  | zero =>
    simp only [Graph.evalWithin, Graph.step, feedback header same]
    rfl
  | succ budget ih =>
    simp only [Graph.evalWithin, Graph.step, feedback header same]
    change ((graph.activation.step (header.operands input) header.heap).map id
      (stationary.feedback input header)).elim some (graph.evalWithin input budget) =
      ((graph.activation.step (header.operands input) header.heap).map id
        (stationary.feedback input header)).elim some (stationary.evalWithin input budget)
    cases graph.activation.step (header.operands input) header.heap with
    | inl result => rfl
    | inr heap => exact ih (stationary.feedback input header heap) same

private theorem coincident_holds : comparison.Holds (model 0) := by
  intro heap word final
  change (∃ budget, graph.evalWithin (input 0) budget (graph.seed (input 0) heap) = some (word, final)) ↔
    ∃ budget, stationary.evalWithin (input 0) budget (graph.seed (input 0) heap) = some (word, final)
  exact exists_congr fun budget => iff_of_eq (congrArg (· = some (word, final))
    (coincident_eval (input 0) budget (graph.seed (input 0) heap) rfl))

example : comparison.HoldsWith (memrefReturns · (model 0)) ∧ comparison.HoldsWith (petriReturns · (model 0)) :=
  ⟨(memref_satisfaction comparison (model 0)).mpr coincident_holds,
    (petri_satisfaction comparison (model 0)).mpr coincident_holds⟩

-- Holding the addresses also returns zero. Its cell 1 still contains 5.
example : memrefReturns stationary (model 1) initial 0 ((afterFirst.write 0 0).write 2 5) :=
  ⟨4, (MemRef.run_eq_evalWithin stationary (input 1) 1 initial).trans rfl⟩

private theorem distinct_rejects : ¬ comparison.Holds (model 1) := by
  intro holds
  obtain ⟨budget, returned⟩ := (holds initial 0 final).mp ⟨2, rfl⟩
  cases budget with
  | zero => cases returned
  | succ budget =>
    have cell := congrArg (fun result : Option (Word × Heap 4) => result.map (fun (_, h) => h 1)) returned
    cases budget <;> (change some (5 : Word) = some 0 at cell; cases cell)

example : (¬ (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 4))
      (translate comparison)) ∧ (¬ comparison.MemRefHolds 4) ∧ (¬ comparison.PetriHolds 4) := by
  have rejected (holds : comparison.HoldsAt 4) := distinct_rejects (holds (input 1))
  obtain ⟨runtime, memref, petri⟩ := satisfaction comparison 4
  exact ⟨rejected ∘ runtime.mp, rejected ∘ memref.mp, rejected ∘ petri.mp⟩

private def tailLoop (value : Origin (activationArgs args) [[.word]] .word) : Graph args :=
  { stationary with activation := ⟨.load (.latest 0) (.arg .head)
      (.store (.latest 0) (.arg copyTo) (.arg zero) (.ret (.latest 1) value)), rfl, zero⟩ }

private def immediate : Sentence captures := .terminates (tailLoop (.arg zero))

private theorem immediate_holds : immediate.HoldsAt 4 := by
  intro input heap
  let loop := tailLoop (.arg zero)
  let header := loop.seed input heap
  let result := loop.activation.body.denote (header.operands input) header.heap
  have stop : (loop.activation.body.denote (header.operands input) header.heap).1 =
      loop.activation.stopWord (header.operands input) := rfl
  refine ⟨result.1, result.2, 0, ?_⟩
  change loop.evalWithin input 0 header = some result
  rw [Graph.evalWithin, Graph.step, Loop.Graph.step, ite_eq_left stop]
  rfl

-- Universal termination quantifies over all inputs and heaps at four cells.
example : (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 4)) (translate immediate) ∧
    immediate.MemRefHolds 4 ∧ immediate.PetriHolds 4 := by
  obtain ⟨runtime, memref, petri⟩ := satisfaction immediate 4
  exact ⟨runtime.mpr immediate_holds, memref.mpr immediate_holds, petri.mpr immediate_holds⟩

private def spin := tailLoop (.output 0 .head)

private def spinHeap := initial.write 2 0

private theorem spin_step :
    spin.step (input 1) (spin.seed (input 1) spinHeap) = .inr (spin.seed (input 1) spinHeap) := by
  change Sum.inr (Header.mk (0 : Address 4) 1 (spinHeap.write 2 0)) =
    Sum.inr (Header.mk (0 : Address 4) 1 spinHeap)
  exact congrArg (fun heap => Sum.inr (Header.mk (0 : Address 4) 1 heap))
    (Function.update_idem _ _ _)

private theorem spin_no_return (budget : Nat) :
    spin.evalWithin (input 1) budget (spin.seed (input 1) spinHeap) = none := by
  induction budget with
  | zero => rw [Graph.evalWithin, spin_step]; rfl
  | succ _ ih => rw [Graph.evalWithin, spin_step]; exact ih

-- The unbounded observation is absent, and the typed CFG has no address-decoder fault.
example (fuel : Nat) : runtimeObserve spin (model 1) spinHeap = Part.none ∧
    (((MemRef.lower 4 spin).run (MemRef.evalBody (input 1)) fuel .nil).run ⟨spinHeap⟩).isSome = true := by
  refine ⟨(runtimeObserve_eq_none_iff_native spin (model 1) spinHeap).mpr ?_,
    MemRef.cfg_run_isSome spin (input 1) fuel ⟨spinHeap⟩⟩
  rintro word final ⟨budget, returned⟩
  change spin.evalWithin (input 1) budget (spin.seed (input 1) spinHeap) = some (word, final) at returned
  rw [spin_no_return] at returned
  cases returned

private def continuing : Sentence captures := .terminates spin

example : (¬ (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime 4))
      (translate continuing)) ∧ (¬ continuing.MemRefHolds 4) ∧ (¬ continuing.PetriHolds 4) := by
  have rejected (holds : continuing.HoldsAt 4) : False := by
    obtain ⟨word, final, budget, returned⟩ := holds (input 1) spinHeap
    rw [spin_no_return] at returned
    cases returned
  obtain ⟨runtime, memref, petri⟩ := satisfaction continuing 4
  exact ⟨rejected ∘ runtime.mp, rejected ∘ memref.mp, rejected ∘ petri.mp⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
