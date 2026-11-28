module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs

/-! # A checked loop whose false edge goes directly to the merge -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Bypass

open CF.Example (add constant result count decrement input num positive regs selector stride zero test)
open Diamond.Prune (Checked carriedMask prune)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)

/-- Entry 4, split 2, true arm 5 → 0, false edge 2 → 3, merge 3, latch 1. -/
def source : Source Op regs num 6 := fun id =>
  if id = 4 then
    ⟨[constant selector 2, constant decrement 255, constant zero 0], .transfer (.jump 2)⟩
  else if id = 2 then
    ⟨[add selector selector decrement, positive selector, add result result stride],
      .branch test (.jump 5) (.jump 3)⟩
  else if id = 5 then
    ⟨[add result result stride], .transfer (.jump 0)⟩
  else if id = 0 then
    ⟨[add result result stride], .transfer (.jump 3)⟩
  else if id = 3 then
    ⟨[add result result zero], .transfer (.jump 1)⟩
  else
    ⟨[add count count decrement, positive count], .branch test (.jump 2) (.ret result)⟩

def checked : Program source 4 :=
  (check source 4).get (by rfl)

abbrev mask := carriedMask checked

def accepted : Checked checked mask :=
  (prune checked).get (by rfl)

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 4 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  ((lower accepted).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat)

def runRVSDG (activations : Nat) : Option Nat :=
  (accepted.lower.run (Join.model model) activations input).map (fun values => (values.get .head).toNat)

def predecessors (activations : Nat) : List Nat :=
  (checked.trace model activations ((source 4).body.eval model input)).map
    (fun occurrence => (checked.predecessor occurrence).val)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Bypass
