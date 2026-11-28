module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Frame)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example (word Inputs input)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)

#guard observe false == some ([3, 0, 2, 4], 2, [1, 0], [none, none, some 3])
#guard (observe true).isNone
#guard (prepare? (loop false) ⟨first.header, 2⟩ 1).isNone
#guard (prepare? (loop false) first 1).isNone

-- The consumer is at position three after reordering, then position two after hoisting.
private def reordered :=
  Header.Sequence.run? (Header.Sequence.initial (Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.lower (loop false)))
    first.header

#guard (reordered.bind fun state => Header.Priority.resolve? state 2) == some 3
#guard ((prepare? (loop false) first 2).map fun prepared =>
  (findCandidate? 3 0 savedOrigins (prepared.intermediate.2.block .header)).isNone) == some true

-- The saved operand is unavailable one cut earlier in the same preheader.
#guard ((prepare? (loop false) first 2).map fun prepared =>
  let _ := targetDecEq (saved := prepared.intermediate.1) (carried := word) (result := word)
  Dominance.Placement.checkCut prepared.intermediate.2 intermediateBlocks
    prepared.consumer.operands prepared.consumer.uses ⟨none, 0⟩) == some false

-- The successor use is the false edge's argument zero, resolved at its source cut.
#guard ((prepare? (loop false) first 2).map fun prepared =>
  match prepared.consumer.uses with
  | [.ordinary ⟨some ⟨_, .header⟩, 3⟩, use@(.phi (some ⟨_, .header⟩) .onFalse 0)] =>
    (use.point? prepared.intermediate.2).map Point.cut == some 4
  | _ => false) == some true

private def viewFrame {saved : Width} : Frame (Label saved word word) → Nat × List Nat
  | ⟨.header, .cons value (.cons old .nil)⟩ => (1, [value.toNat, old.toNat])
  | ⟨.exit, .cons value .nil⟩ => (2, [value.toNat])

private def transfers (output : Output Inputs word word) : Option (List (Nat × List Nat)) := do
  let values := input 2 10 1
  let .inl entry := output.2.entry.eval evalOp (fun term env => term.eval env) values | none
  let .inl once := (output.2.block entry.label).eval evalOp (fun term env => term.eval env)
    (entry.args.append values) | none
  let .inl twice := (output.2.block once.label).eval evalOp (fun term env => term.eval env)
    (once.args.append values) | none
  let .inl exit := (output.2.block twice.label).eval evalOp (fun term env => term.eval env)
    (twice.args.append values) | none
  pure ([entry, once, twice, exit].map viewFrame)

#guard ((prepare? (loop false) first 2).bind fun prepared => transfers prepared.intermediate) ==
  some [(1, [2, 3]), (1, [2, 7]), (1, [2, 11]), (2, [3])]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Regression
