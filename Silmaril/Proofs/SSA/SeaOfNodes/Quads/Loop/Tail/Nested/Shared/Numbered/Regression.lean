module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered

open Diamond.MLIR.CF.Example (input width)
open Shared.MLIR.CF.Example (outerOverlap plan runCF runSource trace)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open RVSDG.NestedTheta.Petri (Finishes)
open Example (layout mergeValues packets runNumbered sourceBudget)

example : (Shared.check outerOverlap 0).isNone = true := rfl
example : layout = some (2, [1, 1], 1) := by decide +kernel
example : trace = [(.innerTrue, 7, 15, 5), (.innerFalse, 32, 65, 5), (.outerFalse, 130, 130, 2)] := rfl
example : mergeValues = [some 15, some 65, some 130] := rfl
example : packets = [some (1, 2, 15), some (1, 1, 65), some (0, 0, 130)] := by
  simp only [packets, Example.headerStates, List.map_cons, List.map_nil, activation_run]
  rfl
example : [0, 1, 2, 3].map sourceBudget = [1, 8, 15, 19] := rfl

example : (runSource 19, runCF 20, runNumbered 3) = (some 130, some 130, some 130) := by
  unfold runNumbered
  rw [lower_run plan model 3 input]
  rfl

example : (runSource 18, runCF 19, runNumbered 2) = (none, none, none) := by
  unfold runNumbered
  rw [lower_run plan model 2 input]
  rfl

example : Finishes (Join.model model) (lower plan) input (.cons (130 : Word width) .nil) :=
  (petri_finishes_iff plan model input (130 : Word width)).mpr ⟨19, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered
