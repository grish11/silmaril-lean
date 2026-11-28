module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Correctness

/-! # The certified carried projection preserves CF routing and returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (Names NamesAgree encodeValues valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open RVSDG (Tuple)
open Silmaril.MLIR.CF (Frame)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked HeaderProjection)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
/-- A projected block reconstructs the same outgoing source frame. -/
theorem projectedBlock_eval {Labels : List Width → Type}
    {jumpTo : JumpTo regs size Labels} {frame : Fin size → Bank (regs := regs) model → Frame Labels}
    (routes : JumpAgrees jumpTo frame) (exit : Labels [valueWidth out]) (block : SourceBlock Op regs out size)
    (projected : HeaderProjection block.body mask) {Γ : List Width} (env : Env Γ)
    (old : Bank (regs := regs) model) :
    (lowerProjectedBlockWith jumpTo exit block projected Γ).eval evalOp (fun term env => term.eval env)
        ((encodeValues (mask.project old)).append env) =
      let next := block.body.eval model old
      .inl (destinationFrameWith frame (returnFrame exit) next (block.terminator.select model next)) :=
  Proofs.projectedBlock_eval routes exit block projected env old

section Source

variable {header : Fin size} (projected : HeaderProjection (src header).body mask)
variable {Γ : List Width} (names : Tuple (Names Γ) (dataPorts regs)) (env : Env Γ)

/-- Each emitted terminator selects the original source destination and
passes its final bank, projecting only when the destination is the header. -/
theorem source_site_frame_with (old : Bank (regs := regs) model) (id : Fin size) :
    let current := siteFrame header mask (out := out) id old
    let next := (src id).body.eval model old
    ((lowerSourceWith src entry header projected names).block current.label).eval evalOp (fun term env => term.eval env)
        (current.args.append env) =
      .inl (destinationFrameWith (siteFrame header mask) (exitFrame header mask) next
        ((src id).terminator.select model next)) :=
  Proofs.source_site_frame_with (entry := entry) projected names env old id

/-- From any original block the typed frame carries exactly the source
input bank, with projection when that block is the header. -/
theorem lowerSourceWith_from_run (fuel : Nat) (id : Fin size) (old : Bank (regs := regs) model) :
    (lowerSourceWith src entry header projected names).runFrom evalOp (fuel + 1) env
        (siteFrame header mask id old) =
      (src.runFrom model fuel id old).map (fun value => Env.cons (valueBits value) .nil) :=
  Proofs.lowerSourceWith_from_run (entry := entry) projected names env fuel id old

/-- At a header-only projection, CF spends one extra visit on the typed return. -/
theorem lowerSourceWith_run (fuel : Nat) (input : Bank (regs := regs) model)
    (ok : NamesAgree env names input) :
    (lowerSourceWith src entry header projected names).run evalOp (fuel + 1) env =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  Proofs.lowerSourceWith_run projected names env fuel input ok

end Source

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

/-- An external argument layout with a matching valuation uses the same
source visit accounting and the original successor frames. -/
theorem lowerWith_run {Γ : List Width} (names : Tuple (Names Γ) (dataPorts regs)) (env : Env Γ)
    (fuel : Nat) (input : Bank (regs := regs) model) (ok : NamesAgree env names input) :
    (lowerWith checked names).run evalOp (fuel + 1) env =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  Proofs.lowerWith_run checked names env fuel input ok

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
