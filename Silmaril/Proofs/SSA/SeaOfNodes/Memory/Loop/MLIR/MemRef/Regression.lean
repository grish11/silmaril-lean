module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef

open Fixture
open RVSDG (Tuple)
open RVSDG.MLIR.Graph.Feedback (Code)
open RVSDG.OrderedRuntime.Structured (Values)
open Silmaril.MLIR.MemRef (Buffer Ty Value)

private def operationNames {scope : List (List (Ty 3))} {outs : List (Ty 3)} :
    Code (Op 3) scope outs → List String
  | .prim op _ rest => op.name :: operationNames rest
  | .yield _ | .choose .. | .feedback .. => []

#guard operationNames (lowerActivation 3 shift).val ==
  ["memref.load", "memref.load", "memref.store", "memref.store", "arith.cmpi ne"]

private def summarize (result : Tuple (Values (Value 3)) (activationPorts 3) × Buffer 3) :
    Nat × Word × Word × Word × Word :=
  let (.cons test values, final) := result
  (test.down.val, values.get .head, final.cell 0, final.cell 1, final.cell 2)

-- Exit and restart both retain the stores and the untouched third cell.
#guard summarize (runActivation shift input ⟨initial 0⟩) == (0, 0, 2, 0, 99)
#guard summarize (runActivation shift input ⟨initial 1⟩) == (1, 1, 2, 0, 99)

-- The next activation sees the just-written head in the same buffer.
#guard summarize (runActivation shift input (runActivation shift input ⟨initial 1⟩).2) == (1, 2, 0, 0, 99)

private def sameCell : Tuple (Val 1) args :=
  .cons (0 : Address 1) (.cons (0 : Address 1) (.cons (0 : Word) .nil))

private def runOne (old : Word) : Nat × Word × Word :=
  let (.cons test values, final) := runActivation shift sameCell ⟨fun _ => old⟩
  (test.down.val, values.get .head, final.cell 0)

-- At the smallest admitted buffer these two addresses coincide. The
-- returned word precedes the stores, and the last store supplies cell zero.
#guard runOne 0 == (0, 0, 0)
#guard runOne 1 == (1, 1, 0)

private def nonzeroStop : Tuple (Val 1) args :=
  .cons (0 : Address 1) (.cons (0 : Address 1) (.cons (7 : Word) .nil))

-- The tail compares against the captured stop value after the stores.
#guard match observeActivation shift nonzeroStop ⟨fun _ => 7⟩ with
  | .inl (word, final) => word == 7 && final.cell 0 == 7
  | .inr _ => false

#guard match observeActivation shift nonzeroStop ⟨fun _ => 8⟩ with
  | .inl _ => false
  | .inr final => final.cell 0 == 7

example (empty : Tuple (Val 0) args) : False :=
  Fin.elim0 (empty.get .head)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef
