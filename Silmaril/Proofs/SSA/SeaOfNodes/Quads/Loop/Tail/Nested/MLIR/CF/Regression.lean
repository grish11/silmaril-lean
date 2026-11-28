module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF

open Diamond.MLIR.CF.Example (input num regs result test)
open Diamond.MLIR.CF.Pruned (headerFrame siteFrame)
open Example (checked incomingResults mask predecessors projected runCF runSource source)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)

example : predecessors = [3, 2, 4] := rfl
example : incomingResults = [7, 6, 10] := rfl
example : mask.kept.length = 6 := rfl
example : mask.rename test = none := rfl

private def first := (source 0).body.eval model input
private def merge (old : Blocks.Bank (regs := regs) model) :=
  (checked.pathQuads (checked.selected model old)).eval model old
private def feedback (old : Blocks.Bank (regs := regs) model) :=
  (source 6).body.eval model ((source 5).body.eval model (merge old))
private def second := feedback first
private def third := feedback second

example : [first, second, third].map (checked.selected model) = [.innerTrue, .innerFalse, .outerFalse] := rfl
example : [first, second, third].map (fun old => ((merge old).get result).toNat) = [7, 8, 16] := rfl
example : [first, second, third].map (fun old => checked.mergeVisits (checked.selected model old)) =
    [3, 2, 2] := rfl

private def emittedEdge (id : Fin 7) (old : Blocks.Bank (regs := regs) model) :=
  let frame := siteFrame checked.header mask (out := num) id old
  ((lower checked projected).block frame.label).eval evalOp (fun term env => term.eval env)
    (frame.args.append (encodeValues input))

private def postOuter (old : Blocks.Bank (regs := regs) model) := (source 1).body.eval model old

example : emittedEdge 3 ((source 2).body.eval model (postOuter first)) =
    .inl (siteFrame checked.header mask 5 (merge first)) := rfl
example : emittedEdge 2 (postOuter second) = .inl (siteFrame checked.header mask 5 (merge second)) := rfl
example : emittedEdge 4 (postOuter third) = .inl (siteFrame checked.header mask 5 (merge third)) := rfl
example : emittedEdge 6 ((source 5).body.eval model (merge first)) =
    .inl (headerFrame checked.header mask second) := rfl
example : emittedEdge 6 ((source 5).body.eval model (merge second)) =
    .inl (headerFrame checked.header mask third) := rfl

example : (runSource 14, runCF 15) = (some 16, some 16) := rfl
example : (runSource 13, runCF 14) = (none, none) := rfl

example : (Diamond.check source 0).isNone = true := rfl

private def skipsMerge : Source Op regs num 7 := fun id =>
  if id = 2 then {source id with terminator := .branch test (.jump 3) (.jump 6)}
  else source id

example : (check skipsMerge 0).isNone = true := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF
