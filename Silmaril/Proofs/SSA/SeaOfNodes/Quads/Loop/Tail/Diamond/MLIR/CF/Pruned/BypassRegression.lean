module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Bypass

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned

open CF.Example (input num regs result test)
open Example.Bypass (accepted checked mask predecessors runCF runRVSDG runSource source)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)

example : (checked.armPath 0).blocks = [5, 0] := rfl
example : (checked.armPath 1).blocks = [] := rfl
example : predecessors 3 = [0, 2, 0] := rfl
example : (checked.trace model 3 ((source 4).body.eval model input)).map
    checked.activationCost = [5, 3, 5] := rfl
example : mask.kept.length = 6 := rfl
example : mask.rename test = none := rfl

private def firstHeader := (source 4).body.eval model input
private def secondHeader := checked.nextBank model firstHeader
private def bypassBank := (source 2).body.eval model secondHeader

-- The direct false occurrence sends the post-header definition to the merge.
example : (secondHeader.get result).toNat = 11 := rfl
example : (bypassBank.get result).toNat = 13 := rfl
example : ((lower accepted).block .header).eval evalOp (fun term env => term.eval env)
    ((encodeValues (mask.project secondHeader)).append (encodeValues input)) =
    .inl (siteFrame checked.header mask 3 bypassBank) := rfl

example : runSource 14 = some 19 := rfl
example : runCF 15 = some 19 := rfl
example : runRVSDG 3 = some 19 := by
  unfold runRVSDG
  rw [accepted.lower_run]
  rfl
example : runSource 13 = none := rfl
example : runCF 14 = none := rfl
example : runRVSDG 2 = none := by
  unfold runRVSDG
  rw [accepted.lower_run]
  rfl

private def cyclicArm : Source Op regs num 6 := fun id =>
  if id = 0 then {source id with terminator := .transfer (.jump 5)} else source id

example : (check cyclicArm 4).isNone = true := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned
