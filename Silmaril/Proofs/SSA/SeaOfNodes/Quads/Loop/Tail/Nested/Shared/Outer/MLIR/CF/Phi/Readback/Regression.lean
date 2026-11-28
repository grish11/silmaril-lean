module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Example
  (rebuiltBanks checks directTargets gammaMatches)

example : rebuiltBanks = [
    ((6, 0), [3, 2, 15, 1, 255, 0, 1]),
    ((7, 0), [1, 0, 150, 1, 255, 0, 0])] := rfl

example : checks = (true, false, false) := rfl

example : gammaMatches = true := by
  unfold gammaMatches
  simp only [List.all_cons, List.all_nil, Outer.Numbered.outer_run]
  rfl

example : directTargets = [some 2, some 7] := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback
