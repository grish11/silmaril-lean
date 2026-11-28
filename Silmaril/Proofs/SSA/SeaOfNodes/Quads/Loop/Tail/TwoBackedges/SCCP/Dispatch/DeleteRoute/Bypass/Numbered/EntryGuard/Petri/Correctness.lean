module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri.Proofs

open SeaOfNodes.Diamond (ValueSort Val)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width}

theorem completed_packet_eq (target : Target regs result) (input : Bank (regs := regs) model)
    {completed expected : Tuple (Val Word) [.value (.data result)]} {fuel : Nat}
    (fired : Finishes (Join.model model) target.2 input completed)
    (returned : target.2.run (Join.model model) fuel input = some expected) : completed = expected := by
  have numbered := (finishes_iff (Join.model model) target.2 input completed).mp fired
  obtain ⟨first, allCompleted⟩ := target.2.returns_eventually (Join.model model) input completed numbered
  obtain ⟨second, allExpected⟩ := target.2.returns_eventually (Join.model model) input expected ⟨fuel, returned⟩
  exact Option.some.inj ((allCompleted (max first second) (Nat.le_max_left ..)).symm.trans
    (allExpected (max first second) (Nat.le_max_right ..)))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.EntryGuard.Petri.Proofs
