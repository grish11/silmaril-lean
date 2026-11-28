module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry

open CategoryTheory
open Fixture
open RVSDG (Tuple)
open SeaOfNodes.Loop (Incoming)
open RVSDG.OrderedRuntime.Structured (Threaded)
open Memory.Diamond.Institution renaming Signature → EntrySignature

private abbrev scope : EntrySignature := ⟨args⟩
private def entry : Entry args 3 := ⟨input 1, initial 7⟩

private def swapPorts : scope ⟶ scope :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail p) => .tail (.tail p)⟩

private def swappedEntry : Entry args 3 :=
  ⟨.cons (1 : Address 3) (.cons (0 : Address 3) (.cons (9 : Word) (.cons (0 : Word) .nil))), initial 7⟩

-- The complete payload round-trips after a nonidentity address-port map.
example : decode (reindex swapPorts swappedEntry.encode) = some entry := by
  rw [decode_reindex, decode_encode]
  rfl

private def feedback : RawEntry args 3 := Petri.encodeArrival .backedge entry.heap entry.input

-- The same well-typed addresses and heap arrive with the wrong occurrence.
example : decode feedback = none := rfl
example : ¬ Admissible feedback := (decode_eq_none_iff feedback).mp rfl
example : decode (reindex swapPorts feedback) = none := by
  rw [decode_reindex]
  rfl

private theorem switched_return :
    observe graph entry.encode = Part.some (encodeResult 0 afterFeedback) :=
  (observe_eq_some_iff_native graph (decode_encode entry) 0 afterFeedback).mpr ⟨1, rfl⟩

example : observe (mapGraph swapPorts graph) swappedEntry.encode = Part.some (encodeResult 0 afterFeedback) := by
  rw [observe_mapGraph swapPorts graph _ (admissible_encode swappedEntry), reindex_encode]
  exact switched_return

private def reversed : Graph args := mapGraph swapPorts graph
private def equation : Equation scope := ⟨graph, reversed⟩
private def reversedFinal : Heap 3 := (initial 7).write 1 9

private theorem reversed_return :
    observe reversed entry.encode = Part.some (encodeResult 0 reversedFinal) :=
  (observe_eq_some_iff_native reversed (decode_encode entry) 0 reversedFinal).mpr ⟨0, rfl⟩

-- The valid entry gives word zero on both sides but preserves different
-- first cells. Whole-tuple comparison rejects the runtime equation.
example : ¬ Holds equation 3 := by
  intro holds
  have equal := holds entry.encode (admissible_encode entry)
  change observe graph entry.encode = observe reversed entry.encode at equal
  rw [switched_return, reversed_return] at equal
  have cellZero := congrArg (fun output : Tuple (WireVal 3) (Threaded wordPorts) =>
    output.get (.tail .head) (0 : Address 3)) (Part.some_inj.mp equal)
  exact (by decide : (9 : Word) ≠ 7) cellZero

private def aliasEntry : Entry args 3 := ⟨input 0, afterEntry⟩

private theorem fixed_heap (arrival : Incoming) :
    graph.step (input 0) arrival afterEntry = .inr afterEntry := by
  have selected : graph.operands (input 0) arrival = graph.operands (input 0) .entry := by
    cases arrival <;> rfl
  rw [Graph.step, selected]
  change Sum.inr (afterEntry.write 0 9) = Sum.inr afterEntry
  apply congrArg Sum.inr
  funext cell
  by_cases chosen : cell = 0
  · subst cell
    simp [Heap.write, afterEntry]
  · simp [Heap.write, chosen]

private theorem no_budget (budget : Nat) (arrival : Incoming) :
    graph.evalWithin (input 0) budget arrival afterEntry = none := by
  induction budget generalizing arrival with
  | zero => simp only [Graph.evalWithin, fixed_heap, Sum.elim_inr]
  | succ budget ih => simpa only [Graph.evalWithin, fixed_heap, Sum.elim_inr] using ih .backedge

-- Successful validation and an absent finite observation are compatible.
example : observe graph aliasEntry.encode = Part.none := by
  apply (observe_eq_none_iff_native graph (decode_encode aliasEntry)).mpr
  intro word final
  rintro ⟨budget, evaluated⟩
  change graph.evalWithin (input 0) budget .entry afterEntry = some (word, final) at evaluated
  rw [no_budget] at evaluated
  cases evaluated

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry
