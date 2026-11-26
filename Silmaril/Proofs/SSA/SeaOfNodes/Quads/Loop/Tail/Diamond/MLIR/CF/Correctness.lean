module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Segment.Thms
import Silmaril.SSA.SeaOfNodes.Quads.CFG.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.MLIR.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Proofs

open SeaOfNodes.Diamond (Dataflow Val ValueSort dataPorts sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model opcode opcode_eval evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Block Cfg Frame)
open RVSDG (Tuple Locals Wires extend)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

theorem entryNames_agree (bank : Bank (regs := regs) model) :
    NamesAgree (encodeValues bank) (entryNames regs) bank := by
  induction regs with
  | nil => intro _ port; cases port
  | cons slot rest ih =>
    cases bank with
    | cons value tail =>
      intro _ port
      cases port with
      | head => rfl
      | tail port => exact weaken_names (ih tail) (valueBits value) port

theorem blockNames_agree {extra : List Width} (captures : Env extra)
    (bank : Bank (regs := regs) model) :
    NamesAgree ((encodeValues bank).append captures) (blockNames extra regs) bank := by
  induction regs with
  | nil => intro _ port; cases port
  | cons slot rest ih =>
    cases bank with
    | cons value tail =>
      intro _ port
      cases port with
      | head => rfl
      | tail port => exact weaken_names (ih tail) (valueBits value) port

section Emission

variable {Labels : List Width → Type} {jump : JumpTo regs size Labels}
variable {frame : Fin size → Bank (regs := regs) model → Frame Labels}
variable {exit : Labels [valueWidth out]}
variable {Γ : List Width} {args : List (SeaOfNodes.Diamond.Ty Width)}
variable {past sigs : List (List (SeaOfNodes.Diamond.Ty Width))}
variable {scope : Scope args past Γ} {env : Env Γ} {input : Tuple (Val Word) args}
variable {locals : Locals (Val Word) past}

private theorem destination_eval (routes : JumpAgrees jump frame)
    (ok : scope.Agrees env input locals) (versions : Wires args past (dataPorts regs))
    (destination : Destination regs out size) :
    (lowerDestinationWith jump exit scope versions destination).eval env =
      destinationFrameWith frame (returnFrame exit) (versions.read input locals) destination := by
  cases destination with
  | jump id => exact routes ok versions id
  | ret result =>
    have observed := ok.resolve (versions.get result)
    change _ = valueBits (SeaOfNodes.Diamond.read model (versions.get result) input locals) at observed
    rw [← Quads.read_get model versions input locals result] at observed
    exact congrArg (fun bits => Frame.mk exit (.cons bits .nil)) observed

private theorem terminator_eval (routes : JumpAgrees jump frame)
    (ok : scope.Agrees env input locals) (versions : Wires args past (dataPorts regs))
    (term : Tail.Terminator regs out size) :
    (lowerTerminatorWith jump exit scope versions term).eval env =
      .inl (destinationFrameWith frame (returnFrame exit) (versions.read input locals)
        (term.select model (versions.read input locals))) := by
  cases term with
  | transfer dest => exact congrArg Sum.inl (destination_eval routes ok versions dest)
  | branch test yes no =>
    let bank := versions.read input locals
    have bit := ok.resolve (versions.get test)
    change _ = valueBits (s := .predicate) (SeaOfNodes.Diamond.read model (versions.get test) input locals) at bit
    rw [← Quads.read_get model versions input locals test] at bit
    have getBit (b : Bool) : (BitVec.ofBool b).getLsbD 0 = b := by cases b <;> rfl
    have guard : (env.get (scope.resolveValue (versions.get test))).getLsbD 0 =
        (bank.get test).down :=
      (congrArg (fun bits : BitVec 1 => bits.getLsbD 0) bit).trans (getBit _)
    change Sum.inl (if (env.get (scope.resolveValue (versions.get test))).getLsbD 0
      then (lowerDestinationWith jump exit scope versions yes).eval env
      else (lowerDestinationWith jump exit scope versions no).eval env) = _
    rw [guard, destination_eval routes ok versions yes, destination_eval routes ok versions no]
    change Sum.inl (if (bank.get test).down then destinationFrameWith frame (returnFrame exit) bank yes
        else destinationFrameWith frame (returnFrame exit) bank no) =
      .inl (destinationFrameWith frame (returnFrame exit) bank (if (bank.get test).down then yes else no))
    cases (bank.get test).down <;> rfl

theorem transfer_eval (routes : JumpAgrees jump frame) (ok : scope.Agrees env input locals)
    (flow : Dataflow Op args past sigs) (versions : Wires args (extend past sigs) (dataPorts regs))
    (term : Tail.Terminator regs out size) :
    (lowerCode opcode flow scope (fun final => lowerTerminatorWith jump exit final versions term)).eval
        evalOp (fun term env => term.eval env) env =
      let bank := versions.read input (flow.eval model input locals)
      .inl (destinationFrameWith frame (returnFrame exit) bank (term.select model bank)) := by
  refine lowerCode_eval opcode evalOp model.run opcode_eval flow scope env input locals ok _ _ _ ?_
  intro _ _ _ finalOk
  exact terminator_eval routes finalOk versions term

theorem block_eval_with (routes : JumpAgrees jump frame) (block : SourceBlock Op regs out size)
    (scope : Scope (dataPorts regs) [] Γ) (env : Env Γ) (old : Bank (regs := regs) model)
    (ok : NamesAgree env scope.inputs old) :
    (lowerBlockWith jump exit block scope).eval evalOp (fun term env => term.eval env) env =
      let bank := block.body.eval model old
      .inl (destinationFrameWith frame (returnFrame exit) bank (block.terminator.select model bank)) := by
  unfold lowerBlockWith
  rw [transfer_eval routes (past := []) (locals := PUnit.unit) ⟨ok, trivial⟩]
  dsimp only
  have bank := CFG.compileBlock_read (past := []) block.body model old PUnit.unit (initial regs)
  rw [Quads.read_initial model] at bank
  rw [bank]

end Emission

private theorem fullJump_agrees : JumpAgrees (fullJump (regs := regs) (out := out) (size := size)) siteFrame :=
  fun ok versions id => congrArg (fun args => Frame.mk (Label.site id) args) (ok.operands_eval (ins := regs) versions)

private theorem block_eval {Γ : List Width} (block : SourceBlock Op regs out size)
    (scope : Scope (dataPorts regs) [] Γ) (env : Env Γ) (old : Bank (regs := regs) model)
    (ok : NamesAgree env scope.inputs old) :
    (lowerBlock block scope).eval evalOp (fun term env => term.eval env) env =
      .inl (destinationFrame (block.body.eval model old)
        (block.terminator.select model (block.body.eval model old))) :=
  block_eval_with fullJump_agrees block scope env old ok

variable (p : Program src entry)

theorem entry_eval (input : Bank (regs := regs) model) :
    (lower p).entry.eval evalOp (fun term env => term.eval env) (encodeValues input) =
      .inl (destinationFrame ((src entry).body.eval model input)
        ((src entry).terminator.select model ((src entry).body.eval model input))) :=
  block_eval _ _ _ _ (entryNames_agree input)

theorem site_eval (input bank : Bank (regs := regs) model) (id : Fin size) :
    ((lower p).block (.site id)).eval evalOp (fun term env => term.eval env)
        ((encodeValues bank).append (encodeValues input)) =
      .inl (destinationFrame ((src id).body.eval model bank)
        ((src id).terminator.select model ((src id).body.eval model bank))) :=
  block_eval _ _ _ _ (blockNames_agree (encodeValues input) bank)

/-- Every source exit makes one additional CF visit. This induction works
for both full and projected source-to-CF frame relations. -/
theorem runBlock_eq_of_frames {Labels : List Width → Type}
    (cfg : Cfg TargetOp Labels (Widths regs) [valueWidth out]) (input : Bank (regs := regs) model)
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
      (src.runFrom model fuel id old).map (fun value => Env.cons (valueBits value) .nil) := by
  induction fuel generalizing Γ id old with
  | zero =>
    rw [Cfg.runBlock, step]
    rfl
  | succ fuel ih =>
    rw [Cfg.runBlock, step]
    simp only [Tail.Source.runFrom]
    cases (src id).terminator.select model ((src id).body.eval model old) with
    | jump site => exact ih site _ _ _ (siteEval site _)
    | ret _ =>
      simp only [destinationFrameWith, returnFrame]
      rw [exitBlock]
      rfl

theorem from_run (input : Bank (regs := regs) model) (fuel : Nat) (id : Fin size)
    (old : Bank (regs := regs) model) :
    (lower p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame id old) =
      (src.runFrom model fuel id old).map (fun value => Env.cons (valueBits value) .nil) :=
  runBlock_eq_of_frames (lower p) input siteFrame .exit (fun id old => site_eval p input old id) rfl
    fuel id old _ _ (site_eval p input old id)

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  runBlock_eq_of_frames (lower p) input siteFrame .exit (fun id old => site_eval p input old id) rfl
    fuel entry input _ _ (entry_eval p input)

theorem split_frame (input old : Bank (regs := regs) model) :
    ((lower p).block (.site p.header)).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (siteFrame (p.armStart (p.selected model old)) ((src p.header).body.eval model old)) := by
  rw [site_eval p, p.splitEdge]
  unfold Program.selected Program.stage
  simp only [Tail.Terminator.select, Join.Choice.eval]
  split <;> simp_all [destinationFrame, destinationFrameWith, Program.armStart]
  rfl

private theorem last_edge {join site : Fin size} (path : Chain.Segment src join site) :
    (src path.lastBlock).terminator = .transfer (.jump join) := by
  induction path with
  | last _ edge => exact edge
  | jump _ _ _ ih => exact ih

theorem predecessor_frame (input old : Bank (regs := regs) model) (occurrence : Fin 2) :
    ((lower p).block (.site (p.predecessor occurrence))).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (siteFrame p.join ((src (p.predecessor occurrence)).body.eval model old)) := by
  have edge : (src (p.predecessor occurrence)).terminator = .transfer (.jump p.join) :=
    last_edge (p.armPath occurrence)
  rw [site_eval p, edge]
  rfl

theorem arm_run (input bank : Bank (regs := regs) model) (occurrence : Fin 2) (fuel : Nat) :
    (lower p).runFrom evalOp (fuel + (p.armPath occurrence).blocks.length + 1)
        (encodeValues input) (siteFrame (p.armStart occurrence) bank) =
      (lower p).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame p.join ((p.armPath occurrence).quads.eval model bank)) := by
  rw [from_run p, from_run p, (p.armPath occurrence).run_segment model]

theorem latch_frame (input old : Bank (regs := regs) model) :
    ((lower p).block (.site p.latch)).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      let next := (src p.latch).body.eval model old
      .inl (if (next.get p.again).down then siteFrame p.header next else exitFrame (next.get p.result)) := by
  rw [site_eval p, p.latchEdge]
  simp only [Tail.Terminator.select]
  split <;> simp_all [destinationFrame, destinationFrameWith]

theorem native_run (activations : Nat) (input : Bank (regs := regs) model) :
    (lower p).run evalOp (p.sourceVisits model activations input + 1) (encodeValues input) =
      (p.lower.run (Join.model model) activations input).map
        (fun values => Env.cons (valueBits (s := out) (values.get .head)) .nil) := by
  rw [lower_run p, p.lower_run]
  cases src.runFrom model (p.sourceVisits model activations input) entry input <;> rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Proofs
