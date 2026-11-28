module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered

open Diamond.MLIR.CF.Example (input width)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example
  (crossesInnerPrefix headerStates layout mergeValues outerValues packets plan runNumbered runSource source
  sourceBudget trace)

example : (Shared.check source 0).isNone = true := rfl
example : (Outer.check crossesInnerPrefix 0).isNone = true := by decide +kernel
example : plan.blockOrder.map Fin.val = [0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 8, 9] := rfl
example : plan.suffix.blocks.map Fin.val = [5, 6] := rfl
example : plan.outerSuffix.blocks.map Fin.val = [10, 11] := rfl
example : (plan.innerEdgeOccurrence true, plan.innerEdgeOccurrence false) = ((3, 0), (4, 0)) := rfl
example : layout = some (6, 2, [1, 1], 1) := by decide +kernel

example : trace = [(.innerTrue, (6, 0), 7), (.innerFalse, (6, 0), 7), (.outerFalse, (7, 0), 4)] := rfl

example : outerValues = [some 15, some 73, some 150] := by
  simp only [outerValues, headerStates, List.map_cons, List.map_nil, outer_run]
  rfl

example : mergeValues = [some 17, some 75, some 152] := by
  simp only [mergeValues, headerStates, List.map_cons, List.map_nil, merge_run]
  rfl

example : packets = [some (1, 2, 17), some (1, 1, 75), some (0, 0, 152)] := by
  simp only [packets, headerStates, List.map_cons, List.map_nil, activation_run]
  rfl

example : [0, 1, 2, 3].map sourceBudget = [1, 10, 19, 25] := rfl

example : (runSource 25, runNumbered 3) = (some 152, some 152) := by
  unfold runNumbered
  rw [lower_run plan model 3 input]
  rfl

example : (runSource 24, runNumbered 2) = (none, none) := by
  unfold runNumbered
  rw [lower_run plan model 2 input]
  rfl

example : Finishes (Join.model model) (lower plan) input (.cons (152 : Word width) .nil) :=
  (petri_finishes_iff plan model input (152 : Word width)).mpr ⟨25, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered
