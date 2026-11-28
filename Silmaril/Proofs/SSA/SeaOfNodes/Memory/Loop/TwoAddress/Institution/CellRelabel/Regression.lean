module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellRelabel.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellRelabel.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open RVSDG (Port Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open CellRelabel (Permutation heap)

private abbrev captures : EntrySignature := ⟨[.address, .address, .word]⟩

private def stop : Port (activationArgs captures.args) .word := .tail (.tail (.tail (.tail .head)))

-- Clear the first cell before reading the second, then write back the
-- first load at the second address. The second load is the tail test.
private def body : Memory.Graph (activationArgs captures.args) :=
  .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg .head) (.arg stop)
      (.load (.latest 1) (.arg (.tail .head))
        (.store (.latest 1) (.arg (.tail .head)) (.output 1 .head)
          (.ret (.latest 2) (.output 0 .head)))))

private def graph : Graph captures.args :=
  ⟨⟨body, rfl, stop⟩, .head, .tail .head, .tail .head, .head⟩

private def swapCells : Permutation 2 := Equiv.swap 0 1

private abbrev model : EntryModel captures :=
  ⟨2, .cons (0 : Address 2) (.cons (1 : Address 2) (.cons (0 : Word) .nil))⟩

private def initial : Heap 2 := fun cell => if cell = 0 then 7 else 5

private def afterFeedback : Heap 2 := (initial.write 0 0).write 1 7

private def final : Heap 2 := (afterFeedback.write 1 0).write 0 7

private theorem returned : nativeReturns graph model initial 0 final := ⟨1, rfl⟩

-- Both live lanes really move and remain distinct under the permutation.
example : (graph.seed (relabelModel model swapCells).input (heap swapCells initial)).first = (1 : Address 2) ∧
    (graph.seed (relabelModel model swapCells).input (heap swapCells initial)).second = (0 : Address 2) := ⟨rfl, rfl⟩

example : (graph.seed (relabelModel model swapCells).input (heap swapCells initial)).first ≠
    (graph.seed (relabelModel model swapCells).input (heap swapCells initial)).second := by
  change (1 : Address 2) ≠ 0
  decide

private def program := RuntimeRoom.GeneratedProgram.lower graph

private theorem observed : program.observe model initial = Part.some (encodeResult 0 final) :=
  (program.observe_eq_some_iff_native model initial 0 final).mpr returned

example : program.petriObserve (relabelModel model swapCells) (heap swapCells initial) =
    Part.some (encodeResult 0 (heap swapCells final)) := by
  rw [program.petriObserve_relabel model swapCells initial, program.petriObserve_eq_numbered model initial,
    observed, Part.map_some,
    relabelOutput_encode]

private def summary (result : Option (Word × Buffer 2)) : Option (Word × Word × Word) :=
  result.map fun (word, buffer) => (word, buffer.cell 0, buffer.cell 1)

-- The actual MemRef CFG observes the swapped full output after one backedge.
#guard (MemRef.run graph model.input 0 ⟨initial⟩).isNone
#guard (MemRef.run graph (relabelModel model swapCells).input 0 ⟨heap swapCells initial⟩).isNone
#guard summary (MemRef.run graph model.input 1 ⟨initial⟩) == some (0, 7, 0)
#guard summary (MemRef.run graph (relabelModel model swapCells).input 1 ⟨heap swapCells initial⟩) ==
  some (0, 0, 7)

private def coincident : Graph captures.args := { graph with entrySecond := .head }

private def equation : RuntimeRoom.Sentence captures :=
  RuntimeRoom.Sentence.lower (.equation graph coincident)

private theorem rejects : ¬ equation.Holds model := by
  intro holds
  let other := RuntimeRoom.GeneratedProgram.lower coincident
  let finalOther := (initial.write 0 0).write 0 7
  have otherObserved : other.observe model initial = Part.some (encodeResult 0 finalOther) :=
    (other.observe_eq_some_iff_native model initial 0 finalOther).mpr ⟨0, rfl⟩
  have agrees : program.observe model initial = other.observe model initial := holds initial
  have equal := Part.some_inj.mp (observed.symm.trans (agrees.trans otherObserved))
  have cell := congrArg (fun output => output.get (.tail .head) (1 : Address 2)) equal
  change (0 : Word) = 5 at cell
  exact (by decide : (0 : Word) ≠ 5) cell

-- Relabeling does not erase the differing heap observation of this equation.
example : ¬ PetriRoom.Holds equation (relabelModel model swapCells) := fun holds =>
  rejects ((PetriRoom.holds_iff_numbered equation model).mp ((PetriRoom.holds_relabel equation model swapCells).mp holds))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
