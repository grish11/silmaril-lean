module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered (petri_finishes_iff)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example
  (activation completion)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (plan)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input width)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example (rows)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example renaming rows → outerRows
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)

set_option maxHeartbeats 1000000 in
example : completion := by
  unfold completion
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨bank, marked, _, packet⟩ := outer_packet plan input (activation i) outerRows
    exact ⟨bank, marked, packet⟩
  · exact inner_waiting_packet plan input (activation 0) rows (by rfl)
  · exact inner_waiting_packet plan input (activation 1) rows (by rfl)
  · exact bypass plan (activation 2) (by rfl)
  · exact (petri_finishes_iff plan model input (152 : Word width)).mpr ⟨25, rfl⟩
