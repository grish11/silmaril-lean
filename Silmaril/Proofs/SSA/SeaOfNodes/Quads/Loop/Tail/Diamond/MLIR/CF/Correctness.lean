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

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model opcode opcode_eval evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Cfg)
open RVSDG (Tuple Locals Wires)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

private theorem entryNames_agree (bank : Bank (regs := regs) model) :
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

private theorem blockNames_agree {extra : List Width} (captures : Env extra)
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

private theorem destination_eval {Γ : List Width} {past : List (List (SeaOfNodes.Diamond.Ty Width))}
    {scope : Scope (dataPorts regs) past Γ} {env : Env Γ} {input : Bank (regs := regs) model}
    {locals : Locals (SeaOfNodes.Diamond.Val Word) past}
    (ok : scope.Agrees env input locals) (versions : Wires (dataPorts regs) past (dataPorts regs))
    (destination : Destination regs out size) :
    (lowerDestination scope versions destination).eval env =
      destinationFrame (versions.read input locals) destination := by
  cases destination with
  | jump id =>
    exact congrArg (fun args => Silmaril.MLIR.CF.Frame.mk (Label.site id) args)
      (ok.operands_eval (ins := regs) versions)
  | ret result =>
    have observed := ok.resolve (versions.get result)
    change _ = valueBits (SeaOfNodes.Diamond.read model (versions.get result) input locals) at observed
    rw [← Quads.read_get model versions input locals result] at observed
    exact congrArg (fun bits => Silmaril.MLIR.CF.Frame.mk Label.exit (.cons bits .nil)) observed

private theorem terminator_eval {Γ : List Width} {past : List (List (SeaOfNodes.Diamond.Ty Width))}
    {scope : Scope (dataPorts regs) past Γ} {env : Env Γ} {input : Bank (regs := regs) model}
    {locals : Locals (SeaOfNodes.Diamond.Val Word) past}
    (ok : scope.Agrees env input locals) (versions : Wires (dataPorts regs) past (dataPorts regs))
    (term : Tail.Terminator regs out size) :
    (lowerTerminator scope versions term).eval env =
      .inl (destinationFrame (versions.read input locals) (term.select model (versions.read input locals))) := by
  cases term with
  | transfer dest => exact congrArg Sum.inl (destination_eval ok versions dest)
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
      then (lowerDestination scope versions yes).eval env
      else (lowerDestination scope versions no).eval env) = _
    rw [guard, destination_eval ok versions yes, destination_eval ok versions no]
    change Sum.inl (if (bank.get test).down then destinationFrame bank yes else destinationFrame bank no) =
      .inl (destinationFrame bank (if (bank.get test).down then yes else no))
    cases (bank.get test).down <;> rfl

private theorem block_eval {Γ : List Width} (block : SourceBlock Op regs out size)
    (scope : Scope (dataPorts regs) [] Γ) (env : Env Γ) (old : Bank (regs := regs) model)
    (ok : NamesAgree env scope.inputs old) :
    (lowerBlock block scope).eval evalOp (fun term env => term.eval env) env =
      .inl (destinationFrame (block.body.eval model old)
        (block.terminator.select model (block.body.eval model old))) := by
  let compiled := CFG.compileBlock block.body (initial regs)
  refine lowerCode_eval opcode evalOp model.run opcode_eval compiled.flow scope env old PUnit.unit
    ⟨ok, trivial⟩ (fun final => lowerTerminator final compiled.outgoing block.terminator)
    (fun term env => term.eval env) _ ?_
  intro Δ final env finalOk
  have bank := CFG.compileBlock_read (past := []) block.body model old PUnit.unit (initial regs)
  rw [Quads.read_initial model] at bank
  rw [terminator_eval finalOk, bank]

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

theorem from_run (input : Bank (regs := regs) model) (fuel : Nat) (id : Fin size)
    (old : Bank (regs := regs) model) :
    (lower p).runFrom evalOp (fuel + 1) (encodeValues input) (siteFrame id old) =
      (src.runFrom model fuel id old).map (fun value => Env.cons (valueBits value) .nil) := by
  induction fuel generalizing id old with
  | zero =>
    change (lower p).runBlock evalOp (encodeValues input) 1 ((lower p).block (.site id))
      ((encodeValues old).append (encodeValues input)) = none
    rw [Cfg.runBlock, site_eval p]
    rfl
  | succ fuel ih =>
    change (lower p).runBlock evalOp (encodeValues input) (fuel + 1 + 1) ((lower p).block (.site id))
      ((encodeValues old).append (encodeValues input)) = _
    rw [Cfg.runBlock, site_eval p]
    simp only [Tail.Source.runFrom]
    cases (src id).terminator.select model ((src id).body.eval model old) with
    | jump _ => exact ih _ _
    | ret _ => rfl

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) := by
  cases fuel with
  | zero =>
    unfold Cfg.run
    rw [Cfg.runBlock, entry_eval p]
    rfl
  | succ fuel =>
    have taken : (src entry).terminator.select model ((src entry).body.eval model input) = .jump p.header := by
      rw [p.entryEdge]
      rfl
    unfold Cfg.run
    rw [Cfg.runBlock, entry_eval p, taken]
    simp only [Tail.Source.runFrom, taken]
    exact from_run p input fuel p.header _

theorem split_frame (input old : Bank (regs := regs) model) :
    ((lower p).block (.site p.header)).eval evalOp (fun term env => term.eval env)
        ((encodeValues old).append (encodeValues input)) =
      .inl (siteFrame (p.armStart (p.selected model old)) ((src p.header).body.eval model old)) := by
  rw [site_eval p, p.splitEdge]
  unfold Program.selected Program.stage
  simp only [Tail.Terminator.select, Join.Choice.eval]
  split <;> simp_all [destinationFrame, Program.armStart]
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
  split <;> simp_all [destinationFrame]

theorem native_run (activations : Nat) (input : Bank (regs := regs) model) :
    (lower p).run evalOp (p.sourceVisits model activations input + 1) (encodeValues input) =
      (p.lower.run (Join.model model) activations input).map
        (fun values => Env.cons (valueBits (s := out) (values.get .head)) .nil) := by
  rw [lower_run p, p.lower_run]
  cases src.runFrom model (p.sourceVisits model activations input) entry input <;> rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Proofs
