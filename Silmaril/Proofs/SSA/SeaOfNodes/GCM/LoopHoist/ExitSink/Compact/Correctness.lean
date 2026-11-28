module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel SavedBank TargetCfg exitId)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Typed (edgePackets)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)

variable {Input Γ Δ full kept bank results args extra : List Width}
variable {w saved carried result : Width}
variable {source : TargetCfg Input saved carried result extra full} {emission : Emission source}

private theorem indices_iff (widths : List Width) (keep : Nat → Bool) (index : Nat) :
    index ∈ (Projection.ofPredicate widths keep).indices ↔ index < widths.length ∧ keep index = true := by
  induction widths generalizing keep index with
  | nil => simp [Projection.ofPredicate, Projection.indices]
  | cons _ rest ih =>
    cases first : keep 0 <;> cases index <;>
      simp [Projection.ofPredicate, Projection.indices, first, List.mem_map, ih]

theorem packet_indices (emission : Emission source) (index : Nat) :
    index ∈ emission.projection.indices ↔ index < full.length ∧ index ∈ emission.scan.inputs := by
  simpa [Emission.projection, Projection.forReads] using
    indices_iff full emission.scan.inputs.contains index

theorem packet_used (emission : Emission source) :
    ∃ scan, scanExit? (emission.cfg.block .exit) = some scan ∧
      ∀ index < emission.projection.types.length, index ∈ scan.inputs := by
  have covered := emission.covered
  unfold packetUsed? at covered
  split at covered
  · contradiction
  · rename_i scan checked
    refine ⟨scan, checked, fun index inBounds => ?_⟩
    simpa using List.all_eq_true.mp covered index (List.mem_range.mpr inBounds)

private def Agree (rename : PartialRename Γ Δ) (before : Env Γ) (after : Env Δ) : Prop :=
  ∀ {w} {ref : Var Γ w} {mapped : Var Δ w}, rename ref = some mapped → after.get mapped = before.get ref

private theorem keep_agree {rename : PartialRename Γ Δ} {before : Env Γ} {after : Env Δ}
    (agree : Agree rename before after) (value : BitVec w.val) :
    Agree (keepUnder rename) (.cons value before) (.cons value after) := by
  intro _ ref mapped checked
  cases ref with
  | here => cases checked; rfl
  | there ref =>
    obtain ⟨prior, translated, rfl⟩ := Option.map_eq_some_iff.mp checked
    exact agree translated

private theorem drop_agree {rename : PartialRename Γ Δ} {before : Env Γ} {after : Env Δ}
    (agree : Agree rename before after) (value : BitVec w.val) :
    Agree (dropUnder rename) (.cons value before) after := by
  intro _ ref mapped checked
  cases ref with
  | here => cases checked
  | there ref => exact agree checked

private theorem projection_agree (p : Projection full) (packet : Env full) (input : Env Input) :
    Agree p.rename (packet.append input) ((p.values packet).append input) := by
  induction p with
  | nil =>
    cases packet
    intro _ ref mapped checked
    cases checked
    rfl
  | keep p ih =>
    cases packet with
    | cons value rest => exact keep_agree (ih rest) value
  | drop p ih =>
    cases packet with
    | cons value rest => exact drop_agree (ih rest) value

private theorem operands_eval {rename : PartialRename Γ Δ}
    {before : Env Γ} {after : Env Δ} {operands : Operands Γ args} {mapped : Operands Δ args}
    (same : Agree rename before after) (checked : rewriteOperands? rename operands = some mapped) :
    mapped.eval after = operands.eval before := by
  induction operands with
  | nil => cases checked; rfl
  | cons ref rest ih =>
    obtain ⟨head, renamed, checkedTail⟩ := Option.bind_eq_some_iff.mp checked
    obtain ⟨tail, repacked, final⟩ := Option.bind_eq_some_iff.mp checkedTail
    change some (.cons head tail) = some mapped at final
    cases final
    change Env.cons (after.get head) (tail.eval after) = Env.cons (before.get ref) (rest.eval before)
    rw [same renamed, ih repacked]

private theorem exit_eval {mask : List Bool} {rename : PartialRename Γ Δ}
    {old : Block TargetOp (ExitLabel bank full) Γ results} {new : Block TargetOp (ExitLabel bank kept) Δ results}
    (rewritten : rewriteExit? mask rename old = some new)
    {before : Env Γ} {after : Env Δ} (agree : Agree rename before after) :
    ∃ values : Env results,
      old.eval evalOp (fun term env => Terminator.eval env term) before = .inr values ∧
      new.eval evalOp (fun term env => Terminator.eval env term) after = .inr values := by
  induction mask generalizing Γ Δ with
  | nil =>
    cases old with
    | letOp => cases rewritten
    | terminator term =>
      cases term with
      | br => cases rewritten
      | condBr => cases rewritten
      | ret reads =>
        obtain ⟨mapped, checked, rfl⟩ := Option.map_eq_some_iff.mp rewritten
        exact ⟨reads.eval before, rfl, congrArg Sum.inr (operands_eval agree checked)⟩
  | cons drop mask ih =>
    cases old with
    | terminator => cases drop <;> cases rewritten
    | letOp op reads tail =>
      cases drop with
      | true => exact ih rewritten (drop_agree agree (evalOp op (reads.eval before)))
      | false =>
        obtain ⟨mapped, checked, continued⟩ := Option.bind_eq_some_iff.mp rewritten
        obtain ⟨newTail, rest, final⟩ := Option.bind_eq_some_iff.mp continued
        change some (.letOp op mapped newTail) = some new at final
        cases final
        have values := operands_eval agree checked
        obtain ⟨out, oldEval, newEval⟩ := ih rest (keep_agree agree (evalOp op (reads.eval before)))
        refine ⟨out, oldEval, ?_⟩
        simpa only [Code.eval, values] using newEval

theorem project_values (p : Projection full) (packet : Operands Γ full) (env : Env Γ) :
    (p.operands packet).eval env = p.values (packet.eval env) := by
  induction p with
  | nil => cases packet; rfl
  | keep p ih => cases packet; simp only [Projection.operands, Projection.values, Operands.eval, ih]; rfl
  | drop p ih => cases packet; exact ih _

private theorem edge_eval (p : Projection full) (edge : Edge (ExitLabel bank full) Γ) (env : Env Γ) :
    (p.edge edge).eval env = p.frame (edge.eval env) := by
  obtain ⟨label, packet⟩ := edge
  cases label with
  | header => rfl
  | exit =>
    have projected := project_values p packet env
    exact congrArg (fun args => (⟨.exit, args⟩ : Frame (ExitLabel bank p.types))) projected

private theorem term_eval (p : Projection full) (term : Terminator (ExitLabel bank full) results Γ) (env : Env Γ) :
    (p.term term).eval env = (term.eval env).map p.frame id := by
  cases term with
  | br => simp [Projection.term, Terminator.eval, Sum.map, edge_eval]
  | ret => rfl
  | condBr guard yes no =>
    simp only [Projection.term, Terminator.eval, edge_eval]
    cases (env.get guard).getLsbD 0 <;> rfl

private theorem block_eval (p : Projection full) (code : Block TargetOp (ExitLabel bank full) Γ results)
    (env : Env Γ) :
    (code.mapTerm p.term).eval evalOp (fun term vals => Terminator.eval vals term) env =
      (code.eval evalOp (fun term vals => Terminator.eval vals term) env).map p.frame id := by
  induction code with
  | terminator term => exact term_eval p term env
  | letOp op operands tail ih => exact ih (.cons (evalOp op (operands.eval env)) env)

private theorem block_packets (p : Projection full) (code : Block TargetOp (ExitLabel bank full) Γ results)
    (env : Env Γ) :
    (code.mapTerm p.term).eval evalOp edgePackets env =
      (code.eval evalOp edgePackets env).map fun (slot, frame) => (slot, p.frame frame) := by
  induction code with
  | terminator term =>
    cases term <;> simp [Projection.term, Code.mapTerm, Code.eval, edgePackets, edge_eval]
  | letOp op operands tail ih => exact ih (.cons (evalOp op (operands.eval env)) env)

theorem header_packets (emission : Emission source) (env : Env (SavedBank saved carried extra ++ Input)) :
    (emission.cfg.block .header).eval evalOp edgePackets env =
      ((source.block .header).eval evalOp edgePackets env).map fun (slot, frame) =>
        (slot, emission.projection.frame frame) :=
  block_packets emission.projection (source.block .header) env

private theorem code_shape (p : Projection full) (code : Block TargetOp (ExitLabel bank full) Γ results)
    (slot : EdgeSlot) :
    (shape.ofBlock (code.mapTerm p.term)).target slot = ((shape.ofBlock code).target slot).map p.target ∧
    (shape.ofBlock (code.mapTerm p.term)).bindings = (shape.ofBlock code).bindings := by
  induction code with
  | terminator term =>
    refine ⟨?_, rfl⟩
    cases term with
    | ret => cases slot <;> rfl
    | br edge =>
      obtain ⟨label, packet⟩ := edge
      cases label <;> cases slot <;> rfl
    | condBr guard yes no =>
      obtain ⟨yesLabel, yesPacket⟩ := yes
      obtain ⟨noLabel, noPacket⟩ := no
      cases yesLabel <;> cases noLabel <;> cases slot <;> rfl
  | letOp op operands tail ih => exact ⟨ih.1, congrArg (· + 1) ih.2⟩

theorem header_shape (emission : Emission source) (slot : EdgeSlot) :
    (shape emission.cfg (some ⟨_, .header⟩)).target slot =
      ((shape source (some ⟨_, .header⟩)).target slot).map emission.projection.target ∧
    (shape emission.cfg (some ⟨_, .header⟩)).bindings = (shape source (some ⟨_, .header⟩)).bindings :=
  code_shape emission.projection (source.block .header) slot

theorem false_occurrence (emission : Emission source)
    (edge : (shape source (some ⟨_, .header⟩)).target .onFalse = some ⟨full, .exit⟩)
    {argument : Nat} (inPacket : argument < emission.projection.types.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? emission.cfg =
      some ⟨some ⟨_, .header⟩, (shape source (some ⟨_, .header⟩)).bindings⟩ := by
  have shapeFacts := header_shape emission .onFalse
  simp [Use.point?, shapeFacts.1, shapeFacts.2, edge, Projection.target, inPacket]

private theorem runFrom_eq (input : Env Input) (fuel : Nat)
    (frame : Frame (ExitLabel (SavedBank saved carried extra) full)) :
    emission.cfg.runFrom evalOp fuel input (emission.projection.frame frame) =
      source.runFrom evalOp fuel input frame := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
    obtain ⟨label, packet⟩ := frame
    cases label with
    | exit =>
      obtain ⟨values, oldEval, newEval⟩ := exit_eval emission.rewritten
        (projection_agree emission.projection packet input)
      change Cfg.runBlock _ _ _ (fuel + 1) emission.exitCode ((emission.projection.values packet).append input) =
        Cfg.runBlock _ _ _ (fuel + 1) (source.block .exit) (packet.append input)
      simp only [Cfg.runBlock, oldEval, newEval]
    | header =>
      have agreement := block_eval emission.projection (source.block .header) (packet.append input)
      change Cfg.runBlock _ _ _ (fuel + 1) ((source.block .header).mapTerm emission.projection.term)
          (packet.append input) =
        Cfg.runBlock _ _ _ (fuel + 1) (source.block .header) (packet.append input)
      rw [Cfg.runBlock, Cfg.runBlock, agreement]
      cases (source.block .header).eval evalOp (fun term vals => Terminator.eval vals term) (packet.append input) with
      | inl next => exact ih next
      | inr values => rfl

theorem run_eq (emission : Emission source) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have agreement := block_eval emission.projection source.entry input
    change Cfg.runBlock _ _ _ (fuel + 1) (source.entry.mapTerm emission.projection.term) input =
      Cfg.runBlock _ _ _ (fuel + 1) source.entry input
    rw [Cfg.runBlock, Cfg.runBlock, agreement]
    cases source.entry.eval evalOp (fun term vals => Terminator.eval vals term) input with
    | inl next => exact runFrom_eq input fuel next
    | inr values => rfl

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem denotePart (emission : Emission source) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, run_eq emission]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
