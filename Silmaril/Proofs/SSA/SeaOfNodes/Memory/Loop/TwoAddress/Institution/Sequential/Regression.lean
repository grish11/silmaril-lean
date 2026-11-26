module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential

open RVSDG (Port Tuple)
open CellEmbedding (Embedding DisjointImages extend restrict)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

open Fixture

private def program := RuntimeRoom.GeneratedProgram.lower graph

private theorem leftObserved :
    numberedStage program model (restrict left initial) = Part.some (3, leftFinal) := by
  apply (numberedStage_eq_some_iff program model _ 3 leftFinal).mpr
  apply (program.observe_eq_some_iff_native model _ 3 leftFinal).mpr
  change graph.Returns model.input (restrict left initial) 3 leftFinal
  rw [initial, (CellEmbedding.extend_disjoint_spec left right disjoint frame leftInitial rightInitial).1]
  exact ⟨1, rfl⟩

private theorem rightObserved :
    numberedStage program ⟨2, next 3⟩ (restrict right initial) = Part.some (3, rightFinal) := by
  apply (numberedStage_eq_some_iff program ⟨2, next 3⟩ _ 3 rightFinal).mpr
  apply (program.observe_eq_some_iff_native ⟨2, next 3⟩ _ 3 rightFinal).mpr
  change graph.Returns (next 3) (restrict right initial) 3 rightFinal
  rw [initial, (CellEmbedding.extend_disjoint_spec left right disjoint frame leftInitial rightInitial).2.1]
  exact ⟨1, rfl⟩

private theorem sequentialReturn :
    numbered program program (embedModel model left) (fun word => CellEmbedding.input right (next word)) initial =
      Part.some (3, 3, final) := by
  rw [numbered_eq_local program program model next left right disjoint, localObserve, leftObserved, Part.bind_some]
  change (numberedStage program ⟨2, next 3⟩ (restrict right initial)).map _ = _
  rw [rightObserved, Part.map_some]
  rfl

-- Each coloured witness reaches a finite completion. The second starts
-- with the heap and word observed at the first completion.
example : ∃ middle,
    program.Completes (embedModel model left) initial (encodeResult 3 middle) ∧
      program.Completes ⟨6, CellEmbedding.input right (next 3)⟩ middle (encodeResult 3 final) := by
  apply (coloured_eq_some_iff program program (embedModel model left)
    (fun word => CellEmbedding.input right (next word)) initial 3 3 final).mp
  exact (coloured_eq_numbered program program (embedModel model left)
    (fun word => CellEmbedding.input right (next word)) initial).trans sequentialReturn

private def continues : Graph captures.args :=
  { graph with activation :=
    ⟨.load (.latest 0) (.arg .head)
      (.store (.latest 0) (.arg .head) (.arg storeWord) (.ret (.latest 1) (.arg storeWord))), rfl, stop⟩ }

private theorem continues_step (header : Header 2) :
    continues.step (next 3) header =
      .inr (continues.feedback (next 3) header (header.heap.write header.first 22)) := rfl

private theorem continues_no_return (budget : Nat) (header : Header 2) :
    continues.evalWithin (next 3) budget header = none := by
  induction budget generalizing header with
  | zero => rw [Graph.evalWithin, continues_step]; rfl
  | succ budget ih => rw [Graph.evalWithin, continues_step]; exact ih _

private def continuingProgram := RuntimeRoom.GeneratedProgram.lower continues

private theorem continuingAbsent :
    numberedStage continuingProgram ⟨2, next 3⟩ (restrict right initial) = Part.none := by
  apply Part.eq_none_iff.mpr
  rintro ⟨word, finalHeap⟩ observed
  have encoded := (numberedStage_eq_some_iff continuingProgram ⟨2, next 3⟩ _ word finalHeap).mp
    (Part.eq_some_iff.mpr observed)
  obtain ⟨budget, returned⟩ :=
    (continuingProgram.observe_eq_some_iff_native ⟨2, next 3⟩ _ word finalHeap).mp encoded
  change continues.evalWithin (next 3) budget (continues.seed (next 3) (restrict right initial)) =
    some (word, finalHeap) at returned
  rw [continues_no_return] at returned
  contradiction

-- Even with a finite first return, the second loop can have no finite result.
example : numbered program continuingProgram (embedModel model left)
    (fun word => CellEmbedding.input right (next word)) initial = Part.none := by
  rw [numbered_eq_local program continuingProgram model next left right disjoint]
  exact (localObserve_eq_none_iff left right _ _ initial).mpr
    (Or.inr ⟨3, leftFinal, leftObserved, continuingAbsent⟩)

private def run (firstFuel secondFuel : Nat) : Option (Word × Word × List Word) := do
  let .cons word (.cons middle .nil) ← (Petri.lower graph).run (thetaRuntime 6) firstFuel
    (encodeInput initial (CellEmbedding.input left model.input))
  let .cons nextWord (.cons final .nil) ← (Petri.lower graph).run (thetaRuntime 6) secondFuel
    (encodeInput middle (CellEmbedding.input right (next word)))
  return (word, nextWord, (List.finRange 6).map final)

-- The actual numbered runners each execute one backedge. The right
-- stage uses the returned 3 as its stop value.
#guard (run 1 2).isNone
#guard (run 2 1).isNone
#guard run 2 2 == some (3, 3, [11, 73, 11, 22, 91, 22])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential
