module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.MLIR.SCF (For)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Typed (edgePackets)

variable {Input extra Γ args : List Width} {saved carried result w : Width} {index : Nat}
variable {source : Source Input saved carried result extra} {emission : Emission source index}
variable {code : Block TargetOp (Label saved carried result extra) Γ [result]}

private theorem eval_weaken (operands : Operands Γ args) (env : Env Γ) (value : BitVec w.val) :
    (For.renameOperands (Var.there (v := w)) operands).eval (.cons value env) = operands.eval env :=
  evalRenameOperands Var.there env (.cons value env) (fun _ => rfl) operands

theorem packetRefs_eval (input : Env Input) (packet : Env args) :
    (packetRefs Input args).eval (packet.append input) = packet := by
  induction packet with
  | nil => rfl
  | cons head tail ih => simp [packetRefs, Env.append, Operands.eval, Env.get, eval_weaken, ih]

private theorem positions_weaken (operands : Operands Γ args) (slot : Nat) :
    positions 0 (For.renameOperands (Var.there (v := w)) operands) slot = [] := by
  induction operands generalizing slot with
  | nil => rfl
  | cons ref rest ih => simp [For.renameOperands, positions, Var.index, ih]

theorem header_uses (header : Header index code) (cut : Nat) :
    sourceUses index cut code = some [.phi (some ⟨_, .header⟩) .onFalse 0] := by
  induction header generalizing cut with
  | last op operands test feedback =>
    simp [sourceUses, useSitesAt, Var.index, positions_weaken feedback (w := result), positions]
  | keep op operands tail ih => exact ih (cut + 1)

theorem header_slots (header : Header index code) :
    (shape.ofBlock code).target .onFalse = some ⟨_, .exit⟩ ∧
    (shape.ofBlock header.code).target .onTrue = some ⟨_, .header⟩ ∧
    (shape.ofBlock header.code).target .onFalse = exitId ∧
    (shape.ofBlock code).bindings = index + 1 ∧ (shape.ofBlock header.code).bindings = index := by
  induction header with
  | last => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | keep op operands tail ih =>
    obtain ⟨oldFalse, newTrue, newFalse, before, after⟩ := ih
    exact ⟨oldFalse, newTrue, newFalse, congrArg (· + 1) before, congrArg (· + 1) after⟩

theorem source_use_point (emission : Emission source index) :
    (Use.phi (some ⟨_, .header⟩) .onFalse 0).point? source =
      some ⟨some ⟨_, .header⟩, index + 1⟩ := by
  have slots := header_slots emission.header
  unfold Use.point?
  change (do
    let dst ← (shape.ofBlock (source.block .header)).target .onFalse
    if 0 < dst.1.length then
      some (⟨some ⟨_, .header⟩, (shape.ofBlock (source.block .header)).bindings⟩ :
        Point (Label saved carried result extra)) else none) = _
  simp [slots.1, slots.2.2.2.1]

theorem operand_occurrence (emission : Emission source index) {argument : Nat}
    (inPacket : argument < emission.header.opcode.1.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? emission.cfg =
      some ⟨some ⟨_, .header⟩, index⟩ := by
  have slots := header_slots emission.header
  change (do
    let dst ← (shape.ofBlock emission.header.code).target .onFalse
    if argument < dst.1.length then
      some (⟨some ⟨_, .header⟩, (shape.ofBlock emission.header.code).bindings⟩ :
        Point (ExitLabel (SavedBank saved carried extra) emission.header.opcode.1)) else none) = _
  simp [slots.2.2.1, slots.2.2.2.2, exitId, inPacket]

theorem sink_legal (accepted : sink? source index = some emission) :
    Legal emission.cfg emission.operandSites [.ordinary ⟨exitId, 1⟩] ⟨exitId, 0⟩ := by
  have checked := (Option.filter_eq_some_iff.mp accepted).2
  let := targetDecEq (saved := saved) (carried := carried) (extra := extra)
    (args := emission.header.opcode.1)
  exact (Dominance.Placement.checkCut_iff.mp checked).2

theorem entry_packet (entry : Entry code) (exitArgs : List Width) (env : Env Γ) :
    ∃ packet : Env (SavedBank saved carried extra),
      code.eval evalOp (fun term vals => Terminator.eval vals term) env = .inl ⟨.header, packet⟩ ∧
      (entry.code exitArgs).eval evalOp (fun term vals => Terminator.eval vals term) env = .inl ⟨.header, packet⟩ := by
  induction entry with
  | jump packet => exact ⟨packet.eval env, rfl, rfl⟩
  | keep op operands tail ih => exact ih (.cons (evalOp op (operands.eval env)) env)

theorem header_packets (header : Header index code) (env : Env Γ) :
    ((header.code.eval evalOp edgePackets env).map fun (slot, frame) =>
      (slot, restorePacket header.opcode.2 frame)) = code.eval evalOp edgePackets env := by
  induction header with
  | last op operands test feedback =>
    simp [Header.code, Header.opcode, Code.eval, edgePackets, Edge.eval, restorePacket,
      Operands.eval, Env.get, eval_weaken]
  | keep op operands tail ih =>
    exact ih (.cons (evalOp op (operands.eval env)) env)

theorem header_eval (header : Header index code) (env : Env Γ) :
    (header.code.eval evalOp (fun term vals => Terminator.eval vals term) env).map
      (restorePacket header.opcode.2) id = code.eval evalOp (fun term vals => Terminator.eval vals term) env := by
  induction header with
  | last op operands test feedback =>
    simp only [Header.code, Header.opcode, Code.eval, Terminator.eval, Env.get]
    cases (env.get test).getLsbD 0 <;>
      simp [Sum.map, Edge.eval, restorePacket, Operands.eval, Env.get, eval_weaken]
  | keep op operands tail ih => exact ih (.cons (evalOp op (operands.eval env)) env)

private theorem exit_eval (packet : Env emission.header.opcode.1) (input : Env Input) :
    (emission.cfg.block .exit).eval evalOp (fun term vals => Terminator.eval vals term) (packet.append input) =
      .inr (.cons (evalOp emission.header.opcode.2 packet) .nil) := by
  simp [Emission.cfg, Code.eval, Terminator.eval, Operands.eval, Env.get, packetRefs_eval]

private theorem runFrom_eq (input : Env Input) (fuel : Nat)
    (next : Frame (ExitLabel (SavedBank saved carried extra) emission.header.opcode.1)) :
    emission.cfg.runFrom evalOp fuel input next =
      source.runFrom evalOp fuel input (restorePacket emission.header.opcode.2 next) := by
  induction fuel generalizing next with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨label, packet⟩ := next
    cases label with
    | exit =>
      change Cfg.runBlock _ _ _ (fuel + 1) _ (packet.append input) = _
      rw [Cfg.runBlock, exit_eval (emission := emission)]
      simp [Cfg.runFrom, Cfg.runBlock, restorePacket, emission.returns, Code.eval,
        Terminator.eval, Operands.eval, Env.append, Env.get]
    | header =>
      have agreement := header_eval emission.header (packet.append input)
      change Cfg.runBlock _ _ _ (fuel + 1) emission.header.code (packet.append input) =
        Cfg.runBlock _ _ _ (fuel + 1) (source.block .header) (packet.append input)
      rw [Cfg.runBlock, Cfg.runBlock, ← agreement]
      cases (emission.header.code.eval evalOp (fun term vals => Terminator.eval vals term)
        (packet.append input)) with
      | inl frame => exact ih frame
      | inr values => rfl

theorem run_eq (emission : Emission source index) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    obtain ⟨packet, before, after⟩ := entry_packet emission.entry _ input
    change Cfg.runBlock _ _ _ (fuel + 1) _ input = Cfg.runBlock _ _ _ (fuel + 1) _ input
    change emission.cfg.entry.eval evalOp (fun term vals => Terminator.eval vals term) input =
      .inl ⟨.header, packet⟩ at after
    rw [Cfg.runBlock, Cfg.runBlock, before, after]
    exact runFrom_eq input fuel ⟨.header, packet⟩

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem denotePart (emission : Emission source index) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, run_eq emission]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink
