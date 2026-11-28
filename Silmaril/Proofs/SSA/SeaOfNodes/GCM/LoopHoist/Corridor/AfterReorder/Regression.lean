module

import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Regression

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Frame)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Example (loop word Inputs input)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance (stage)

-- Moving the comparison to index zero shifts the hoist candidate to index two.
-- Stale index one names a latch-dependent binding, so its cut stays in the header.
#guard (reordered.map fun (_, state) => state.origins) == some [2, 0, 1, 3]
#guard (reordered.bind fun (_, state) => Header.Priority.resolve? state 1) == some 2
#guard ((reordered.bind fun (_, state) => do
    let ⟨_, binding⟩ ← findBinding 1 0 headerOrigins (state.cfg.block .header)
    let cut ← chooseCfgCut? state.cfg binding.operands binding.uses
    pure (stage cut.block, cut.cut))) == some (1, 0)
#guard (reordered.bind fun (_, state) =>
    hoistCodeWith? state.cfg.entry (state.cfg.block .header) 1 (chooseCfgCut? state.cfg)).isNone

#guard observe 1 == some ([(2, 0)], 3, 3, [none, none, some 2])
#guard (observe 0).isNone

private def viewFrame {saved : Width} : Frame (Label saved word word) → Nat × List Nat
  | ⟨.header, .cons value (.cons old .nil)⟩ => (1, [value.toNat, old.toNat])
  | ⟨.exit, .cons value .nil⟩ => (2, [value.toNat])

private def transfers (output : Output Inputs word word) : Option (List (Nat × List Nat)) := do
  let values := input 2 8 1
  let .inl entry := output.2.entry.eval evalOp (fun term env => term.eval env) values | none
  let .inl once := (output.2.block entry.label).eval evalOp (fun term env => term.eval env)
    (entry.args.append values) | none
  let .inl twice := (output.2.block once.label).eval evalOp (fun term env => term.eval env)
    (once.args.append values) | none
  let .inl exit := (output.2.block twice.label).eval evalOp (fun term env => term.eval env)
    (twice.args.append values) | none
  pure ([entry, once, twice, exit].map viewFrame)

#guard ((replay? (loop false) ⟨[⟨2, 0⟩], 1⟩).bind transfers) ==
    some [(1, [2, 3]), (1, [2, 6]), (1, [2, 9]), (2, [2])]
#guard ((schedule? (loop false) [2] 1).bind fun (_, output) =>
    (output.2.run evalOp 3 (input 8 8 3)).map (fun env => (env.get .here).toNat)) == some 6

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Regression
