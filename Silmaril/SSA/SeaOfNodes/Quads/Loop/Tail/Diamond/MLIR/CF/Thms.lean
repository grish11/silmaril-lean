module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Correctness

/-! # Exact routing and bounded returns for the emitted typed CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF

open SeaOfNodes.Diamond (Dataflow Val ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp evalOp model opcode)
open SeaOfNodes.MLIR.Lowering (NamesAgree Scope encodeValues lowerCode valueBits valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Block Cfg Frame)
open SeaOfNodes.MLIR (Word)
open RVSDG (Locals Tuple Wires extend)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
section Emission

theorem entryNames_agree (bank : Bank (regs := regs) model) :
    NamesAgree (encodeValues bank) (entryNames regs) bank :=
  Proofs.entryNames_agree bank

theorem blockNames_agree {extra : List Width} (captures : Env extra)
    (bank : Bank (regs := regs) model) :
    NamesAgree ((encodeValues bank).append captures) (blockNames extra regs) bank :=
  Proofs.blockNames_agree captures bank

variable {Labels : List Width → Type} {jump : JumpTo regs size Labels}
variable {frame : Fin size → Bank (regs := regs) model → Frame Labels}
variable {exit : Labels [valueWidth out]}

/-- Execute an existing producer transfer and route its final bank. The
transfer may start with a different typed bank than the one it produces. -/
theorem transfer_eval {Γ : List Width} {args : List (SeaOfNodes.Diamond.Ty Width)}
    {past sigs : List (List (SeaOfNodes.Diamond.Ty Width))}
    {scope : Scope args past Γ} {env : Env Γ} {input : Tuple (Val Word) args}
    {locals : Locals (Val Word) past}
    (routes : JumpAgrees jump frame) (ok : scope.Agrees env input locals)
    (flow : Dataflow Op args past sigs) (versions : Wires args (extend past sigs) (dataPorts regs))
    (term : Tail.Terminator regs out size) :
    (lowerCode opcode flow scope (fun final => lowerTerminatorWith jump exit final versions term)).eval
        evalOp (fun term env => term.eval env) env =
      let bank := versions.read input (flow.eval model input locals)
      .inl (destinationFrameWith frame (returnFrame exit) bank (term.select model bank)) :=
  Proofs.transfer_eval routes ok flow versions term

theorem block_eval_with {Γ : List Width} (routes : JumpAgrees jump frame)
    (block : SourceBlock Op regs out size) (scope : Scope (dataPorts regs) [] Γ)
    (env : Env Γ) (old : Bank (regs := regs) model) (ok : NamesAgree env scope.inputs old) :
    (lowerBlockWith jump exit block scope).eval evalOp (fun term env => term.eval env) env =
      let bank := block.body.eval model old
      .inl (destinationFrameWith frame (returnFrame exit) bank (block.terminator.select model bank)) :=
  Proofs.block_eval_with routes block scope env old ok

/-- Reuse the source fuel proof for any emission with exact successor frames
and the same one-block CF return. -/
theorem runBlock_eq_of_frames (cfg : Cfg TargetOp Labels (Widths regs) [valueWidth out])
    (input : Bank (regs := regs) model)
    (frame : Fin size → Bank (regs := regs) model → Frame Labels) (exit : Labels [valueWidth out])
    (siteEval : ∀ id old,
      let current := frame id old
      let next := (src id).body.eval model old
      (cfg.block current.label).eval evalOp (fun term env => term.eval env)
          (current.args.append (encodeValues input)) =
        .inl (destinationFrameWith frame (returnFrame exit) next ((src id).terminator.select model next)))
    (exitBlock : cfg.block exit = .terminator (.ret (.cons .here .nil)))
    (fuel : Nat) (id : Fin size) (old : Bank (regs := regs) model)
    {Γ : List Width} (block : Block TargetOp Labels Γ [valueWidth out]) (env : Env Γ)
    (step :
      let next := (src id).body.eval model old
      block.eval evalOp (fun term env => term.eval env) env =
        .inl (destinationFrameWith frame (returnFrame exit) next ((src id).terminator.select model next))) :
    cfg.runBlock evalOp (encodeValues input) (fuel + 1) block env =
      (src.runFrom model fuel id old).map (fun value => Env.cons (valueBits value) .nil) :=
  Proofs.runBlock_eq_of_frames cfg input frame exit siteEval exitBlock fuel id old block env step

end Emission

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
