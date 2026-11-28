module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF

open Diamond.MLIR.CF.Example (input num width)
open Outer.Numbered.Example (headerStates plan runNumbered runSource trace)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Env)
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example (arrivals runCF successors)

example : trace = [(.innerTrue, (6, 0), 7), (.innerFalse, (6, 0), 7), (.outerFalse, (7, 0), 4)] := rfl

example : arrivals = [some (6, 0, 10, 15), some (6, 0, 10, 73), some (7, 0, 10, 150)] := by
  simp only [arrivals, headerStates, List.map_cons, List.map_nil, outer_arrival]
  rfl

example : successors = [some (.inl (1, 2, 17)), some (.inl (1, 1, 75)), some (.inr 152)] := by
  simp only [successors, headerStates, List.map_cons, List.map_nil, Comparison.latch_successor]
  rfl

private def output : Env [valueWidth num] := .cons (152 : Word width) .nil

private theorem returned : (lower plan).run evalOp 26 (encodeValues input) = some output := by
  rw [show 26 = 25 + 1 by rfl, lower_run plan input 25]
  rfl

example : (runSource 25, runCF 26, runNumbered 3) = (some 152, some 152, some 152) := by
  simp only [runCF, returned]
  unfold runNumbered
  rw [Outer.Numbered.lower_run plan model 3 input]
  rfl

example : (runSource 24, runCF 25, runNumbered 2) = (none, none, none) := by
  unfold runCF runNumbered
  rw [show 25 = 24 + 1 by rfl, lower_run plan input 24, Outer.Numbered.lower_run plan model 2 input]
  rfl

example : ∃ activations, ((Outer.Numbered.lower plan).run (Join.model model) activations input).map
    (encodeValues (ins := [num])) = some output :=
  (Comparison.cf_returns_iff plan input output).mp ⟨26, returned⟩

example : ∃ packet, Finishes (Join.model model) (Outer.Numbered.lower plan) input packet ∧
    encodeValues (ins := [num]) packet = output :=
  (Comparison.cf_finishes_iff plan input output).mp ⟨26, returned⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF
