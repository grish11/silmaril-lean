module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF.Correctness

/-! The original dispatch routing and exact CF execution observations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Tail.Diamond.MLIR.CF (siteFrame)
open Silmaril.MLIR.Arith (Width Env)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width}
variable (p : Program Op regs (.data result)) (input : Bank (regs := regs) model)

/-- Dispatch chooses the original feedback label and passes the current bank. -/
theorem dispatch_frame (bank : Bank (regs := regs) model) :
    ((lower p).block (.site 2)).eval evalOp (fun term env => term.eval env)
        ((encodeValues bank).append (encodeValues input)) =
      .inl (siteFrame (out := .data result) (feedbackBlock (bank.get p.select).down) bank) :=
  Proofs.dispatch_frame p input bank

/-- Each occurrence passes its own full reaching bank to the header. -/
theorem feedback_frame (side : Bool) (bank : Bank (regs := regs) model) :
    ((lower p).block (.site (feedbackBlock side))).eval evalOp (fun term env => term.eval env)
        ((encodeValues bank).append (encodeValues input)) =
      .inl (siteFrame (out := .data result) (1 : Fin 5) ((p.feedback side).eval model bank)) :=
  Proofs.feedback_frame p input side bank

/-- CF spends one extra visit on the typed return block. -/
theorem lower_run (fuel : Nat) :
    (lower p).run evalOp (fuel + 1) (encodeValues input) =
      (p.source.runFrom model fuel 0 input).map (fun value => Env.cons value .nil) :=
  Proofs.lower_run p input fuel

theorem returns_iff (value : Word result) :
    (∃ fuel, (lower p).run evalOp fuel (encodeValues input) = some (.cons value .nil)) ↔
      ∃ fuel, p.source.runFrom model fuel 0 input = some value :=
  Proofs.returns_iff p input value

theorem diverges_iff :
    (lower p).Diverges evalOp (encodeValues input) ↔
      ¬ ∃ value fuel, p.source.runFrom model fuel 0 input = some value :=
  Proofs.diverges_iff p input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.MLIR.CF
