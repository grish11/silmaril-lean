module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbedding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary

open RVSDG (Tuple)
open CellEmbedding (extend restrict)
open Fixture

private abbrev ambient := [ValueSort.address, .address, .word]

-- The second loop has two address captures, then its stop and store words.
-- Only the stop capture reads the first return.
private def wiring : Wiring ambient captures.args :=
  .forward .head (.forward (.tail .head) (.word fun
    | .head => .tail (.tail .head)
    | .tail impossible => nomatch impossible))

private def forwarded : Tuple (Val 6) ambient :=
  .cons (right 0) (.cons (right 1) (.cons (22 : Word) .nil))

private def postHeap : Heap 6 := extend left initial leftFinal

private theorem firstRun :
    (Petri.lower graph).run (thetaRuntime 6) 2
      (encodeInput initial (CellEmbedding.input left model.input)) = some (encodeResult 3 postHeap) := by
  have initialEq : extend left initial leftInitial = initial :=
    (CellEmbedding.eq_extend_iff left initial initial leftInitial).mpr
      ⟨(CellEmbedding.extend_disjoint_spec left right disjoint frame leftInitial rightInitial).1, fun _ _ => rfl⟩
    |>.symm
  rw [Petri.lower_run]
  rw [← initialEq, graph.seed_embed, graph.evalWithin_embed]
  rfl

example : wiring.select 3 forwarded = CellEmbedding.input right (next 3) := rfl

-- Observe the checked numbered packet on the actual first post-heap.
example :
    ((Petri.lower graph).run (thetaRuntime 6) 2
      (encodeInput initial (CellEmbedding.input left model.input))).bind
        (fun (out : Tuple (WireVal 6) (carrier [.word])) =>
          match out with
          | .cons word (.cons middle .nil) => (adapter wiring).run (thetaRuntime 6) 0 (packet word forwarded middle)) =
      some (packet 3 (CellEmbedding.input right (next 3)) postHeap) := by
  rw [firstRun]
  exact adapter_run wiring 0 3 forwarded postHeap

private def run : Option (Word × Word × List Word) := do
  let .cons word (.cons middle .nil) ← (Petri.lower graph).run (thetaRuntime 6) 2
    (encodeInput initial (CellEmbedding.input left model.input))
  let .cons retained nextEntry ← (adapter wiring).run (thetaRuntime 6) 0
    (packet word forwarded middle)
  let .cons nextWord (.cons final .nil) ← (Petri.lower graph).run (thetaRuntime 6) 2 nextEntry
  return (retained, nextWord, (List.finRange 6).map final)

#guard run == some (3, 3, [11, 73, 11, 22, 91, 22])

-- An admitted return consumer reads the selected stop capture separately
-- from the reserved word. This executes the existing numbered splice.
private def inspectStop : Wiring captures.args [.word, .word] :=
  .forward (.tail (.tail .head)) (.word (fun impossible => nomatch impossible))

private def inspect :
    Option (Word × Word × Word × List Word) :=
  ((splice wiring (checked inspectStop)).run (thetaRuntime 6) 0 (packet 3 forwarded postHeap)).map
    (fun | .cons word (.cons selected (.cons copy (.cons heap .nil))) =>
           (word, selected, copy, (List.finRange 6).map heap))

#guard inspect == some (3, 3, 3, [11, 73, 11, 9, 91, 3])

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary
