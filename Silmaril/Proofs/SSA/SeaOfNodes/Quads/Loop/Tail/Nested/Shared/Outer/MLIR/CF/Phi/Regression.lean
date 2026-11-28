module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi

open Diamond.MLIR.CF.Example (input)
open Outer.Numbered.Example (plan runNumbered runSource)
open Outer.MLIR.CF.Example (runCF)
open SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example
  (columns directSelected selected)

example : columns = [((6, 0), [1, 2, 0, 4, 5, 6, 7]), ((7, 0), [1, 2, 0, 4, 5, 6, 7])] := rfl

example : selected = [
    ((6, 0), [3, 2, 15, 1, 255, 0, 1]),
    ((6, 0), [2, 1, 73, 1, 255, 0, 0]),
    ((7, 0), [1, 0, 150, 1, 255, 0, 0])] := rfl

example : directSelected = [((1, 1), [1, 0, 75, 1, 255, 0, 0])] := rfl

example : (runSource 25, runCF 26, runNumbered 3) = (some 152, some 152, some 152) := by
  unfold runCF runNumbered
  rw [show 26 = 25 + 1 by rfl, CF.lower_run plan input 25, Outer.Numbered.lower_run plan model 3 input]
  rfl

example : (runSource 24, runCF 25, runNumbered 2) = (none, none, none) := by
  unfold runCF runNumbered
  rw [show 25 = 24 + 1 by rfl, CF.lower_run plan input 24, Outer.Numbered.lower_run plan model 2 input]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi
