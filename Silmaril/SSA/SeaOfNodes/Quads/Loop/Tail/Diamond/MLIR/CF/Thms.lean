module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Correctness

/-! # Exact routing and bounded returns for the emitted typed CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits)
open Silmaril.MLIR.Arith (Width Env)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry)

/-- The emitted split takes the source occurrence, testing the post-header bank. -/
theorem split_frame (input old : Bank (regs := regs) model) :
    ((lower p).block (.site p.header)).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (siteFrame (p.armStart (p.selected model old)) ((src p.header).body.eval model old)) :=
  Proofs.split_frame p input old

/-- The last original block of each occurrence sends its own final bank to
the common join. The target frame contains these exact typed arguments. -/
theorem predecessor_frame (input old : Bank (regs := regs) model) (occurrence : Fin 2) :
    ((lower p).block (.site (p.predecessor occurrence))).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (siteFrame p.join ((src (p.predecessor occurrence)).body.eval model old)) :=
  Proofs.predecessor_frame p input old occurrence

/-- Running the chosen emitted arm spends one CF visit per original arm
block and continues at the common join with the selected arm's final bank. -/
theorem arm_run (input bank : Bank (regs := regs) model) (occurrence : Fin 2) (fuel : Nat) :
    (lower p).runFrom evalOp (fuel + (p.armPath occurrence).blocks.length + 1)
        (encodeValues input) (siteFrame (p.armStart occurrence) bank) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame p.join ((p.armPath occurrence).quads.eval model bank)) :=
  Proofs.arm_run p input bank occurrence fuel

/-- The latch passes the complete updated bank on feedback and only the
selected return value on exit. -/
theorem latch_frame (input old : Bank (regs := regs) model) :
    ((lower p).block (.site p.latch)).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      let next := (src p.latch).body.eval model old
      .inl (if (next.get p.again).down then siteFrame p.header next else exitFrame (next.get p.result)) :=
  Proofs.latch_frame p input old

/-- CF uses the source visit budget plus one synthetic return visit. The
equation includes absence of a result at insufficient budget. -/
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  Proofs.lower_run p fuel input

/-- The numbered γ/θ graph and the typed CF graph give the same bounded
observation at the exact source cost of the selected native trace plus one. -/
theorem native_run (activations : Nat) (input : Bank (regs := regs) model) :
    (lower p).run evalOp (p.sourceVisits model activations input + 1) (encodeValues input) =
      (p.lower.run (Join.model model) activations input).map
        (fun values => Env.cons (valueBits (s := out) (values.get .head)) .nil) :=
  Proofs.native_run p activations input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF
