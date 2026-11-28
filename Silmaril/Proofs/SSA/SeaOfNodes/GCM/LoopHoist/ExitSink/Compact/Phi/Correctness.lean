module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi

open Silmaril.MLIR.Arith (Atom Env Var Width word)
open Silmaril.MLIR.CF (Block Edge Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes.GCM (EdgeSlot)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel SavedBank TargetCfg)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Typed (edgePackets)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)
open Silmaril.SSA.PhiView

variable {Input bank full Γ Δ : List Width} {saved carried result : Width} {extra : List Width}
variable {source : TargetCfg Input saved carried result extra full}

private theorem edge_operands (p : Projection full) (edge : Edge (ExitLabel bank full) Γ) :
    exitOperands? (p.edge edge) = (exitOperands? edge).map p.operands := by
  rcases edge with ⟨label, operands⟩
  cases label <;> rfl

private theorem term_operands (p : Projection full) (term : Terminator (ExitLabel bank full) Δ Γ)
    (slot : EdgeSlot) :
    (atSlot? (p.term term) slot).bind exitOperands? = ((atSlot? term slot).bind exitOperands?).map p.operands := by
  cases term <;> cases slot <;> first | rfl | exact edge_operands p _

private theorem map_row (p : Projection full) (code : Block TargetOp (ExitLabel bank full) Γ Δ)
    (slot : EdgeSlot) :
    ((atSlot? (terminal (code.mapTerm p.term)).2 slot).bind exitOperands?).map
        (fun args => (⟨_, args⟩ : (scope : List Width) × Operands scope p.types)) =
      (((atSlot? (terminal code).2 slot).bind exitOperands?).map
        (fun args => (⟨_, args⟩ : (scope : List Width) × Operands scope full))).map
          (fun row => (⟨row.1, p.operands row.2⟩ : (scope : List Width) × Operands scope p.types)) := by
  induction code with
  | terminator term =>
    simp only [Silmaril.MLIR.Pure.Code.mapTerm, terminal, term_operands, Option.map_map, Function.comp_def]
  | letOp _ _ _ ih => exact ih

theorem row_project (emission : Emission source) (occ : Occurrence) :
    rowAt? emission.cfg occ = (rowAt? source occ).map fun row => ⟨row.1, emission.projection.operands row.2⟩ := by
  obtain ⟨pred, slot⟩ := occ
  cases pred
  · exact map_row emission.projection source.entry slot
  · exact map_row emission.projection (source.block .header) slot

private theorem edge_values (edge : Edge (ExitLabel bank full) Γ) (env : Env Γ) :
    exitValues? (edge.eval env) = (exitOperands? edge).map (·.eval env) := by
  rcases edge with ⟨label, operands⟩
  cases label <;> rfl

private theorem term_packet (term : Terminator (ExitLabel bank full) Δ Γ) (slot : EdgeSlot) (env : Env Γ) :
    (edgePackets term env).findSome? (fun (actual, frame) => if actual = slot then exitValues? frame else none) =
      ((atSlot? term slot).bind exitOperands?).map (·.eval env) := by
  cases term <;> cases slot <;>
    simp [edgePackets, atSlot?, List.findSome?, edge_values, reduceCtorEq]
  all_goals split <;> rename_i found <;> exact found.symm

private theorem block_packet (code : Block TargetOp (ExitLabel bank full) Γ Δ) (slot : EdgeSlot) (env : Env Γ) :
    (code.eval evalOp edgePackets env).findSome? (fun (actual, frame) => if actual = slot then exitValues? frame else none) =
      ((atSlot? (terminal code).2 slot).bind exitOperands?).map (·.eval (terminalEnv code env)) := by
  induction code with
  | terminator term => exact term_packet term slot env
  | letOp op operands _ ih => exact ih (.cons (evalOp op (operands.eval env)) env)

theorem packet_operands (occ : Occurrence) (env : Env (occ.1.scope Input (SavedBank saved carried extra))) :
    packetAt? source occ env =
      (operandsAt? source occ).map (·.eval (terminalEnv (predecessor source occ.1) env)) :=
  block_packet (predecessor source occ.1) occ.2 env

private theorem map_packet (p : Projection full) (code : Block TargetOp (ExitLabel bank full) Γ Δ)
    (slot : EdgeSlot) (env : Env Γ) :
    ((code.mapTerm p.term).eval evalOp edgePackets env).findSome?
        (fun (actual, frame) => if actual = slot then exitValues? frame else none) =
      ((code.eval evalOp edgePackets env).findSome?
        (fun (actual, frame) => if actual = slot then exitValues? frame else none)).map p.values := by
  induction code with
  | terminator term =>
    simp only [Silmaril.MLIR.Pure.Code.mapTerm, Silmaril.MLIR.Pure.Code.eval, term_packet, term_operands,
      Option.map_map, Function.comp_def, project_values]
  | letOp op operands _ ih => exact ih (.cons (evalOp op (operands.eval env)) env)

theorem packet_project (emission : Emission source) (occ : Occurrence)
    (env : Env (occ.1.scope Input (SavedBank saved carried extra))) :
    packetAt? emission.cfg occ env = (packetAt? source occ env).map emission.projection.values := by
  obtain ⟨pred, slot⟩ := occ
  cases pred
  · exact map_packet emission.projection source.entry slot env
  · exact map_packet emission.projection (source.block .header) slot env

private theorem read_var {w : Width} (v : Var Γ w) (env : Env Γ)
    (tail : Isotope.LambdaSSA.Semantics.Env Atom) :
    (env.toLambdaSSA tail) v.index = word (env.get v) := by
  induction v with
  | here => cases env; rfl
  | there _ ih => cases env; exact ih _

private theorem read_arguments (args : Operands Γ Δ) (env : Env Γ) :
    readArguments (arguments args) env.toLambdaSSA = pack (args.eval env) := by
  induction args with
  | nil => rfl
  | cons v rest ih =>
    change Isotope.Value.pair ((env.toLambdaSSA) v.index)
      (readArguments (arguments rest) env.toLambdaSSA) =
      .pair (word (env.get v)) (pack (rest.eval env))
    rw [read_var, ih]

theorem latch_packet (row : Incoming source) (env : Env (row.val.1.scope Input (SavedBank saved carried extra))) :
    (packetAt? source row.val env).map pack = some (row.latch env) := by
  rw [packet_operands]
  have found := (Option.some_get row.property).symm
  change operandsAt? source row.val = some row.operands at found
  rw [found, Option.map_some, Option.map_some]
  exact congrArg some (read_arguments row.operands (terminalEnv (predecessor source row.val.1) env)).symm

theorem latch_at_packet (occ : Occurrence) (env : Env (occ.1.scope Input (SavedBank saved carried extra))) :
    latchAt? source occ env = (packetAt? source occ env).map pack := by
  unfold latchAt?
  split
  · rename_i present
    exact (latch_packet (source := source) ⟨occ, present⟩ env).symm
  · rename_i absent
    cases found : operandsAt? source occ with
    | none => rw [packet_operands, found]; rfl
    | some _ => exact (absent (by rw [found]; rfl)).elim

private theorem cons_heq {w : Width} (ref : Var Γ w) (types : Δ = full)
    {kept : Operands Γ Δ} {old : Operands Γ full} (same : HEq kept old) :
    HEq (Operands.cons ref kept) (Operands.cons ref old) := by
  subst Δ
  cases same
  rfl

private theorem keep_operands (operands : Operands Γ full) :
    HEq ((Projection.keepAll full).operands operands) operands := by
  induction operands with
  | nil => rfl
  | cons ref _ ih => exact cons_heq ref (Projection.keepAll_types _) ih

private theorem row_heq (types : Δ = full) {kept : Operands Γ Δ} {old : Operands Γ full}
    (same : HEq kept old) :
    HEq (⟨Γ, kept⟩ : (scope : List Width) × Operands scope Δ)
      (⟨Γ, old⟩ : (scope : List Width) × Operands scope full) := by
  subst Δ
  cases same
  rfl

private theorem option_map_heq {α β : Type} (types : β = α) (f : α → β)
    (identity : ∀ a, HEq (f a) a) (value : Option α) : HEq (value.map f) value := by
  subst β
  have same : f = id := funext fun a => eq_of_heq (identity a)
  rw [same, Option.map_id, id_eq]

private theorem pack_packet_heq (types : Δ = full) {left : Option (Env Δ)} {right : Option (Env full)}
    (same : HEq left right) : left.map pack = right.map pack := by
  subst Δ
  exact congrArg (Option.map pack) (eq_of_heq same)

theorem compact_rows_again (first : Emission source) :
    ∃ second : Emission first.cfg, compact? first.cfg = some second ∧
      ∀ occ : Occurrence, HEq (rowAt? second.cfg occ) (rowAt? first.cfg occ) ∧
        ∀ env : Env (occ.1.scope Input (SavedBank saved carried extra)),
          HEq (packetAt? second.cfg occ env) (packetAt? first.cfg occ env) ∧
          latchAt? second.cfg occ env = latchAt? first.cfg occ env := by
  obtain ⟨second, rerun, identity, _, _⟩ := first.compact_again
  have types := (congrArg Projection.types identity).trans (Projection.keepAll_types _)
  refine ⟨second, rerun, fun occ => ⟨?_, fun env => ?_⟩⟩
  · rw [row_project, identity]
    have keepTypes := Projection.keepAll_types first.projection.types
    exact option_map_heq (congrArg (fun widths => (scope : List Width) × Operands scope widths) keepTypes)
      _ (fun row => row_heq keepTypes (keep_operands row.2)) _
  · have packets : HEq (packetAt? second.cfg occ env) (packetAt? first.cfg occ env) := by
      rw [packet_project, identity]
      exact option_map_heq (congrArg Env (Projection.keepAll_types _)) _ Projection.keepAll_values _
    refine ⟨packets, ?_⟩
    rw [latch_at_packet, latch_at_packet]
    exact pack_packet_heq types packets

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi
