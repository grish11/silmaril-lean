module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned

open CF.Example (checked source input count stride test predecessors)
open Pruned.Example (accepted mask headerArities rejects runCF)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)

example : headerArities = (some 7, some 6) := rfl
example : mask.rename test = none := rfl
-- The stride is used in the long arm and the counter is read by the latch.
example : (mask.rename stride).isSome = true := rfl
example : (mask.rename count).isSome = true := rfl
example : rejects stride.index = true := rfl
example : rejects count.index = true := rfl
example : predecessors 3 = [6, 0, 6] := rfl

private def firstHeader := (source 4).body.eval model input
private def secondHeader := checked.nextBank model firstHeader
private def thirdHeader := checked.nextBank model secondHeader
private def firstSplit := (source 2).body.eval model firstHeader
private def secondSplit := (source 2).body.eval model secondHeader

example : (lower accepted).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
    .inl (headerFrame checked.header mask firstHeader) := rfl

example : ((lower accepted).block .header).eval evalOp (fun term env => term.eval env)
    ((encodeValues (mask.project firstHeader)).append (encodeValues input)) =
    .inl (siteFrame checked.header mask 5 firstSplit) := rfl
example : ((lower accepted).block .header).eval evalOp (fun term env => term.eval env)
    ((encodeValues (mask.project secondHeader)).append (encodeValues input)) =
    .inl (siteFrame checked.header mask 0 secondSplit) := rfl

private def afterFive := (source 5).body.eval model firstSplit
private def firstJoin := (source 6).body.eval model afterFive
private def secondJoin := (source 0).body.eval model secondSplit
private def firstLatch := (source 3).body.eval model firstJoin
private def secondLatch := (source 3).body.eval model secondJoin

example : ((lower accepted).block (.site 6 (by decide))).eval evalOp (fun term env => term.eval env)
    ((encodeValues afterFive).append (encodeValues input)) =
    .inl (siteFrame checked.header mask 3 firstJoin) := rfl
example : ((lower accepted).block (.site 0 (by decide))).eval evalOp (fun term env => term.eval env)
    ((encodeValues secondSplit).append (encodeValues input)) =
    .inl (siteFrame checked.header mask 3 secondJoin) := rfl

example : ((lower accepted).block (.site 1 (by decide))).eval evalOp (fun term env => term.eval env)
    ((encodeValues firstLatch).append (encodeValues input)) =
    .inl (headerFrame checked.header mask secondHeader) := rfl
example : ((lower accepted).block (.site 1 (by decide))).eval evalOp (fun term env => term.eval env)
    ((encodeValues secondLatch).append (encodeValues input)) =
    .inl (headerFrame checked.header mask thirdHeader) := rfl

example : runCF 16 = some 22 := rfl
example : runCF 15 = none := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned
