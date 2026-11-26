module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF

open Example (checked source input runSource runCF predecessors)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)

example : (checked.armPath 0).blocks = [5, 6] := rfl
example : (checked.armPath 1).blocks = [0] := rfl
example : predecessors 3 = [6, 0, 6] := rfl

private def firstHeader := (source 4).body.eval model input
private def secondHeader := checked.nextBank model firstHeader
private def firstSplit := (source 2).body.eval model firstHeader
private def secondSplit := (source 2).body.eval model secondHeader
private def afterFive := (source 5).body.eval model firstSplit

-- The split reads its own comparison, even though the previous predicate
-- in the second header's arguments was true.
example : ((lower checked).block (.site 2)).eval evalOp (fun term env => term.eval env)
    ((encodeValues firstHeader).append (encodeValues input)) = .inl (siteFrame 5 firstSplit) := rfl
example : ((lower checked).block (.site 2)).eval evalOp (fun term env => term.eval env)
    ((encodeValues secondHeader).append (encodeValues input)) = .inl (siteFrame 0 secondSplit) := rfl

example : ((lower checked).block (.site 5)).eval evalOp (fun term env => term.eval env)
    ((encodeValues firstSplit).append (encodeValues input)) = .inl (siteFrame 6 afterFive) := rfl
example : ((lower checked).block (.site 6)).eval evalOp (fun term env => term.eval env)
    ((encodeValues afterFive).append (encodeValues input)) =
    .inl (siteFrame 3 ((source 6).body.eval model afterFive)) := rfl
example : ((lower checked).block (.site 0)).eval evalOp (fun term env => term.eval env)
    ((encodeValues secondSplit).append (encodeValues input)) =
    .inl (siteFrame 3 ((source 0).body.eval model secondSplit)) := rfl

private def firstJoin := (source 6).body.eval model afterFive
private def firstLatch := (source 3).body.eval model firstJoin

example : ((lower checked).block (.site 1)).eval evalOp (fun term env => term.eval env)
    ((encodeValues firstLatch).append (encodeValues input)) = .inl (siteFrame 2 secondHeader) := rfl

example : runSource 14 = none := rfl
example : runCF 15 = none := rfl
example : runSource 15 = some 22 := rfl
example : runCF 16 = some 22 := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF
