module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Thms
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (Source SavedBank ExitLabel exitId targetDecEq)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Typed (edgePackets)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier (operations)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra Γ root moved : List Width} {saved carried result w : Width} {cut : Nat}
variable {source : Source Input saved carried result extra} {emission : Emission source cut}
variable {suffix : Block TargetOp (Label saved carried result extra) (moved ++ root) [result]}
variable {original : Block TargetOp (Label saved carried result extra) Γ [result]}

private theorem get_front (front : Env moved) (env : Env root) (ref : Var root w) :
    (front.append env).get (weakenFront moved ref) = env.get ref := by
  induction front with
  | nil => rfl
  | cons head tail ih => exact ih

private theorem get_end (env : Env Γ) (input : Env Input) (ref : Var Γ w) :
    (env.append input).get (weakenEnd ref) = env.get ref := by
  induction ref with
  | here => cases env; rfl
  | there rest ih =>
    cases env with
    | cons head tail => exact ih tail

private theorem scopeRefs_eval (env : Env Γ) : (scopeRefs Γ).eval env = env := by
  induction env with
  | nil => rfl
  | cons value rest ih =>
    simp [scopeRefs, Operands.eval, Env.get, evalRenameOperands Var.there rest (.cons value rest) (fun _ => rfl), ih]

private theorem body_source (body : Body root moved suffix) (front : Env moved) (env : Env root) :
    let packet := body.transfers.2.eval env
    let value := body.value (front.append env)
    suffix.eval evalOp (fun term vals => Terminator.eval vals term) (front.append env) =
      .inl (if (env.get body.transfers.1).getLsbD 0 then ⟨.header, packet⟩
        else ⟨.exit, .cons value .nil⟩) ∧
    suffix.eval evalOp edgePackets (front.append env) =
      [(.onTrue, ⟨.header, packet⟩), (.onFalse, ⟨.exit, .cons value .nil⟩)] := by
  induction body with
  | finish guard feedback value inside =>
    simp [Body.transfers, Body.value, Code.eval, Terminator.eval, edgePackets, Edge.eval, Operands.eval,
      get_front, evalRenameOperands _ env (front.append env) (get_front front env)]
    split <;> simp_all
  | bind op reads tail ih =>
    exact ih (.cons (evalOp op (reads.eval (front.append env))) front)

private theorem body_exit (body : Body root moved suffix) (env : Env (moved ++ root)) (input : Env Input) :
    (body.exitCode Input).eval evalOp (fun term vals => Terminator.eval vals term) (env.append input) =
      .inr (.cons (body.value env) .nil) := by
  induction body with
  | finish =>
    simp [Body.exitCode, Body.value, Code.eval, Terminator.eval, Operands.eval, get_end]
  | bind op reads tail ih =>
    have same := evalRenameOperands weakenEnd env (env.append input) (get_end env input) reads
    simp only [Body.exitCode, Body.value, Code.eval, same]
    exact ih (.cons (evalOp op (reads.eval env)) env)

private theorem header_exit (header : Header cut original) (packet : Env header.packetTypes) (input : Env Input) :
    (header.exitCode Input).eval evalOp (fun term vals => Terminator.eval vals term) (packet.append input) =
      .inr (.cons (header.value packet) .nil) := by
  induction header with
  | split body => exact body_exit body packet input
  | keep _ _ _ ih => exact ih packet

private theorem header_eval (header : Header cut original) (env : Env Γ) :
    (header.code.eval evalOp (fun term vals => Terminator.eval vals term) env).map
      header.restorePacket id = original.eval evalOp (fun term vals => Terminator.eval vals term) env := by
  induction header with
  | split body =>
    have evaluates := (body_source body .nil env).1
    simp only [Env.append] at evaluates
    rw [evaluates]
    simp only [Header.code, Code.eval, Terminator.eval, Edge.eval]
    cases (env.get body.transfers.1).getLsbD 0 <;>
      simp [Sum.map, Header.restorePacket, restorePacketWith, Header.value]
    exact congrArg body.value (scopeRefs_eval env)
  | keep op reads tail ih => exact ih (.cons (evalOp op (reads.eval env)) env)

theorem header_packets (header : Header cut original) (env : Env Γ) :
    ((header.code.eval evalOp edgePackets env).map fun (slot, frame) =>
      (slot, header.restorePacket frame)) = original.eval evalOp edgePackets env := by
  induction header with
  | split body =>
    have packets := (body_source body .nil env).2
    simp only [Env.append] at packets
    rw [packets]
    simp [Header.code, Header.restorePacket, restorePacketWith, Header.value, Code.eval, edgePackets, Edge.eval]
    exact congrArg body.value (scopeRefs_eval env)
  | keep op reads tail ih => exact ih (.cons (evalOp op (reads.eval env)) env)

private theorem body_shape (body : Body root moved suffix) (input : List Width) :
    (shape.ofBlock suffix).target .onTrue = some ⟨_, .header⟩ ∧
    (shape.ofBlock suffix).target .onFalse = some ⟨_, .exit⟩ ∧
    (shape.ofBlock suffix).bindings = (shape.ofBlock (body.exitCode input)).bindings := by
  induction body with
  | finish => exact ⟨rfl, rfl, rfl⟩
  | bind _ _ _ ih => exact ⟨ih.1, ih.2.1, congrArg (· + 1) ih.2.2⟩

private theorem body_nonempty {code : Block TargetOp (Label saved carried result extra) root [result]}
    (body : Body root [] code) (input : List Width) :
    0 < (shape.ofBlock (body.exitCode input)).bindings := by
  cases body with
  | finish _ _ _ inside => simp at inside
  | bind => simp [Body.exitCode, shape.ofBlock]

private theorem header_shape (header : Header cut original) (input : List Width) :
    (shape.ofBlock original).target .onTrue = some ⟨_, .header⟩ ∧
    (shape.ofBlock original).target .onFalse = some ⟨_, .exit⟩ ∧
    (shape.ofBlock header.code).target .onTrue = some ⟨_, .header⟩ ∧
    (shape.ofBlock header.code).target .onFalse = exitId ∧
    (shape.ofBlock header.code).bindings = cut ∧
    (shape.ofBlock original).bindings = cut + (shape.ofBlock (header.exitCode input)).bindings ∧
    0 < (shape.ofBlock (header.exitCode input)).bindings := by
  induction header with
  | split body =>
    obtain ⟨trueSlot, falseSlot, counts⟩ := body_shape body input
    exact ⟨trueSlot, falseSlot, rfl, rfl, rfl, counts.trans (Nat.zero_add _).symm, body_nonempty body input⟩
  | keep _ _ tail ih =>
    obtain ⟨oldTrue, oldFalse, newTrue, newFalse, kept, count, nonempty⟩ := ih
    refine ⟨oldTrue, oldFalse, newTrue, newFalse, congrArg (· + 1) kept, ?_, nonempty⟩
    change (shape.ofBlock _).bindings + 1 = _ + (shape.ofBlock (tail.exitCode input)).bindings
    rw [count, Nat.add_right_comm]

private theorem body_operations (body : Body root moved suffix) (input : List Width) :
    operations (body.exitCode input) = operations suffix := by
  induction body with
  | finish => rfl
  | bind _ _ _ ih => simp only [Body.exitCode, operations, ih]

theorem operation_order (header : Header cut original) (input : List Width) :
    operations header.code = (operations original).take cut ∧
    operations (header.exitCode input) = (operations original).drop cut := by
  induction header with
  | split body => exact ⟨rfl, body_operations body input⟩
  | keep _ _ _ ih =>
    simp only [Header.code, Header.exitCode, operations, List.take_succ_cons, List.drop_succ_cons]
    exact ⟨congrArg (List.cons _) ih.1, ih.2⟩

theorem operand_occurrence (emission : Emission source cut) {argument : Nat}
    (inPacket : argument < emission.header.packetTypes.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? emission.cfg =
      some ⟨some ⟨_, .header⟩, cut⟩ := by
  have facts := header_shape emission.header Input
  change (do
    let dst ← (shape.ofBlock emission.header.code).target .onFalse
    if argument < dst.1.length then
      some (⟨some ⟨_, .header⟩, (shape.ofBlock emission.header.code).bindings⟩ :
        Point (ExitLabel (SavedBank saved carried extra) emission.header.packetTypes)) else none) = _
  simp [facts.2.2.2.1, facts.2.2.2.2.1, exitId, inPacket]

theorem sink_legal (accepted : sinkAt? source cut = some emission)
    {site : Site (ExitLabel (SavedBank saved carried extra) emission.header.packetTypes)}
    (listed : site ∈ sites exitId 0 (emission.cfg.block .exit)) :
    Legal emission.cfg site.operands site.uses site.point := by
  have checked := (Option.filter_eq_some_iff.mp accepted).2
  let := targetDecEq (saved := saved) (carried := carried) (extra := extra) (args := emission.header.packetTypes)
  exact (Dominance.Placement.checkCut_iff.mp (List.all_eq_true.mp checked site listed)).2

private theorem in_cuts (emission : Emission source cut) : cut ∈ cuts source := by
  have facts := header_shape emission.header Input
  apply List.mem_range.mpr
  change cut < (shape.ofBlock (source.block .header)).bindings
  have ⟨counts, nonempty⟩ := facts.2.2.2.2.2
  omega

theorem discover_spec (found : discover? source = some ⟨cut, emission⟩) :
    sinkAt? source cut = some emission ∧
      ∀ {other : Nat} (alternative : Emission source other), sinkAt? source other = some alternative → cut ≤ other := by
  obtain ⟨before, index, after, order, picked, refused⟩ := List.findSome?_eq_some_iff.mp found
  obtain ⟨candidate, accepted, same⟩ := Option.map_eq_some_iff.mp picked
  cases same
  refine ⟨accepted, ?_⟩
  intro other alternative admitted
  have listed := in_cuts alternative
  rw [order] at listed
  have later : other ∉ before := by
    intro earlier
    have failed := refused other earlier
    simp [admitted] at failed
  rcases List.mem_cons.mp ((List.mem_append.mp listed).resolve_left later) with equal | later
  · exact equal.ge
  · have ascending : (cuts source).Pairwise (· ≤ ·) := List.pairwise_le_range
    rw [order] at ascending
    exact (List.pairwise_cons.mp (List.pairwise_append.mp ascending).2.1).1 _ later

theorem discover_none : discover? source = none ↔ ∀ cut, sinkAt? source cut = none := by
  simp only [discover?, List.findSome?_eq_none_iff, Option.map_eq_none_iff]
  refine ⟨fun noneFound cut => ?_, fun all cut _ => all cut⟩
  cases checked : sinkAt? source cut with
  | none => rfl
  | some emission =>
    have failed := noneFound cut (in_cuts emission)
    rw [checked] at failed
    contradiction

private theorem runFrom_eq (input : Env Input) (fuel : Nat)
    (next : Frame (ExitLabel (SavedBank saved carried extra) emission.header.packetTypes)) :
    emission.cfg.runFrom evalOp fuel input next =
      source.runFrom evalOp fuel input (emission.restorePacket next) := by
  induction fuel generalizing next with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨label, packet⟩ := next
    cases label with
    | exit =>
      change Cfg.runBlock _ _ _ (fuel + 1) (emission.header.exitCode Input) (packet.append input) =
        Cfg.runBlock _ _ _ (fuel + 1) (source.block .exit) (.cons (emission.header.value packet) input)
      rw [Cfg.runBlock, header_exit emission.header, emission.returns]
      rfl
    | header =>
      have agreement := header_eval emission.header (packet.append input)
      change Cfg.runBlock _ _ _ (fuel + 1) emission.header.code (packet.append input) =
        Cfg.runBlock _ _ _ (fuel + 1) (source.block .header) (packet.append input)
      rw [Cfg.runBlock, Cfg.runBlock, ← agreement]
      cases (emission.header.code.eval evalOp (fun term vals => Terminator.eval vals term)
        (packet.append input)) with
      | inl frame => exact ih frame
      | inr values => rfl

theorem run_eq (emission : Emission source cut) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    obtain ⟨packet, before, after⟩ := emission.entry.code_packet _ input
    change Cfg.runBlock _ _ _ (fuel + 1) _ input = Cfg.runBlock _ _ _ (fuel + 1) _ input
    change emission.cfg.entry.eval evalOp (fun term vals => Terminator.eval vals term) input =
      .inl ⟨.header, packet⟩ at after
    rw [Cfg.runBlock, Cfg.runBlock, before, after]
    exact runFrom_eq input fuel ⟨.header, packet⟩

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem denotePart (emission : Emission source cut) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, run_eq emission]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix
