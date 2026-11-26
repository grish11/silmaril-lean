module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Correctness

/-! # The certified carried projection preserves CF routing and returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits)
open Silmaril.MLIR.Arith (Width Env)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (checked : Checked p mask)

include checked in
/-- The incoming header frame has fewer typed block arguments. -/
theorem header_smaller (old : Bank (regs := regs) model) :
    (headerFrame p.header mask (out := out) old).argsTy.length < (Widths regs).length := by
  simpa only [headerFrame, List.length_map] using checked.smaller

/-- The projected entry edge passes exactly the kept post-preheader values. -/
theorem entry_frame (input : Bank (regs := regs) model) :
    (lower checked).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      .inl (headerFrame p.header mask ((src entry).body.eval model input)) :=
  Proofs.entry_frame checked input

/-- A source site keeps its exact successor and outgoing values. Only a
header destination projects its argument bank. This also covers the
distinct arm predecessors and the original common-merge block. -/
theorem site_frame (input old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame p.header mask (out := out) id old
    let next := (src id).body.eval model old
    ((lower checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (destinationFrameWith (siteFrame p.header mask) (exitFrame p.header mask) next
        ((src id).terminator.select model next)) :=
  Proofs.site_frame checked input old id

/-- The latch computes the original test and return. Its feedback edge
passes the simultaneous projection of the updated source bank. -/
theorem latch_frame (input old : Bank (regs := regs) model) :
    let current := siteFrame p.header mask (out := out) p.latch old
    let next := (src p.latch).body.eval model old
    ((lower checked).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append (encodeValues input)) =
      .inl (if (next.get p.again).down then headerFrame p.header mask next
        else exitFrame p.header mask (next.get p.result)) :=
  Proofs.latch_frame checked input old

/-- The original source budget and the CF budget still differ by one return
visit, even when a run exhausts. -/
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower checked).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  Proofs.lower_run checked fuel input

theorem run_agrees (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower checked).run evalOp fuel (encodeValues input) = (CF.lower p).run evalOp fuel (encodeValues input) := by
  cases fuel with
  | zero => rfl
  | succ fuel => rw [lower_run, CF.lower_run]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned
