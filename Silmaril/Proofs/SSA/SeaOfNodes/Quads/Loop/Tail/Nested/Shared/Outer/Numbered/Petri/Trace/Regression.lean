module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example
  (observations packets stoppingBank)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example renaming activation → headerAt
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (plan)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input width)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example (rows)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example renaming rows → outerRows
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered (lower)

example : observations =
    [(some ((3, 0), [3, 2, 7, 1, 255, 0, 1]), ((6, 0), [3, 2, 15, 1, 255, 0, 1])),
     (some ((4, 0), [2, 1, 36, 1, 255, 0, 0]), ((6, 0), [2, 1, 73, 1, 255, 0, 0])),
     (none, ((7, 0), [1, 0, 150, 1, 255, 0, 0]))] := rfl


set_option maxHeartbeats 1000000 in
example : ∃ witness : Trace plan input packets stoppingBank,
    packets.map Packets.encode = (Windows.inputs plan witness.windows).map (cfPacketsAt plan rows outerRows input) ∧
    Finishes semantics (lower plan) input (.cons (152 : Word width) .nil) := by
  obtain ⟨first⟩ := activation plan (headerAt 0)
  obtain ⟨second⟩ := activation plan (headerAt 1)
  obtain ⟨last⟩ := activation plan (headerAt 2)
  obtain ⟨witness⟩ := trace_of_windows plan input (.again first (.again second (.stop last)))
  exact ⟨witness, Windows.cf_packets plan input rows outerRows witness.windows, witness.replay⟩
