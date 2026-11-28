module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example.Defs

/-! # Exercise all three occurrences in a loop with two feedback edges -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example

open Diamond.MLIR.CF.Example
  (add constant count decrement input num positive regs result selector stride test width zero)
open Diamond.Prune (HeaderProjection)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)

/-- Entry 0, outer split 1, inner split 2, merge 5, latch 6.
The inner false occurrence goes directly from 2 to 5. -/
def source : Source Op regs num 7 := fun id =>
  if id = 0 then
    ⟨[constant selector 3, constant decrement 255, constant stride 1, constant zero 0], .transfer (.jump 1)⟩
  else if id = 1 then
    ⟨[add selector selector decrement, positive selector], .branch test (.jump 2) (.jump 4)⟩
  else if id = 2 then
    ⟨[add result result stride, ⟨_, _, test, .ult width, .cons stride (.cons selector .nil)⟩],
      .branch test (.jump 3) (.jump 5)⟩
  else if id = 3 then
    ⟨[add result result stride], .transfer (.jump 5)⟩
  else if id = 4 then
    ⟨[add result result result], .transfer (.jump 5)⟩
  else if id = 5 then
    ⟨[add result result zero], .transfer (.jump 6)⟩
  else
    ⟨[add count count decrement, positive count], .branch test (.jump 1) (.ret result)⟩

def checked : Program source 0 := (check source 0).get (by rfl)

abbrev mask := carriedMask checked

def projected : HeaderProjection (source checked.header).body mask :=
  (prune checked).get (by rfl)

def predecessors : List Nat :=
  [.innerTrue, .innerFalse, .outerFalse].map fun occurrence => (checked.predecessor occurrence).val

/-- Read the three compiled columns on the same first header bank. -/
def incomingResults : List Nat :=
  let old := (source 0).body.eval model input
  [.innerTrue, .innerFalse, .outerFalse].map fun occurrence =>
    ((checked.mergeBank model old occurrence).get result).toNat

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 0 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  ((lower checked projected).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example
