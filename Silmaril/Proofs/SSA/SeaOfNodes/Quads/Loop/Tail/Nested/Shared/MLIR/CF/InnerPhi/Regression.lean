module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example
  (gammaMatches parallelColumns trace)
open Outer.Numbered.Example (headerStates)

example : trace = [
    (some ((3, 0), [3, 2, 7, 1, 255, 0, 1]), ((6, 0), [3, 2, 15, 1, 255, 0, 1])),
    (some ((4, 0), [2, 1, 36, 1, 255, 0, 0]), ((6, 0), [2, 1, 73, 1, 255, 0, 0])),
    (none, ((7, 0), [1, 0, 150, 1, 255, 0, 0]))] := rfl

example : gammaMatches = true := by
  simp only [gammaMatches, headerStates, List.all_cons, List.all_nil, gamma_run]
  rfl

example : parallelColumns = [
    ((2, 0), [2, 3, 1, 5, 6, 7, 0]),
    ((2, 1), [2, 3, 1, 5, 6, 7, 0])] := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi
