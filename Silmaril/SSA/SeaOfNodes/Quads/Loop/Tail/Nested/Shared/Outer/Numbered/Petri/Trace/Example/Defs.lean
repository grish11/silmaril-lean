module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Example.Defs

/-! # Three reached activations and one stopping bank -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example

open Diamond.MLIR.CF.Example (regs)
open SeaOfNodes.Loop.MLIR.CF (model)
open MLIR.CF.Phi (pack)
open MLIR.CF.Phi.Example (words)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (plan headerStates)

def packets : List (Packets regs 12) := headerStates.map (packetsAt plan)

def observations : List (Option ((Nat × Nat) × List Nat) × ((Nat × Nat) × List Nat)) :=
  packets.map fun packet =>
    let format := fun (row : (Fin 12 × Fin 2) × Silmaril.MLIR.Arith.Env (Diamond.MLIR.CF.Widths regs)) =>
      ((row.1.1.val, row.1.2.val), words (pack row.2))
    (packet.encode.1.map format, format packet.encode.2)

def stoppingBank := nextBank plan model (activation 2)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example
