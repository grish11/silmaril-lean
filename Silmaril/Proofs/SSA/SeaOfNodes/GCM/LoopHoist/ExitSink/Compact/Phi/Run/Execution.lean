module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Edge Terminator)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel SavedBank TargetCfg)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)

variable {Input bank full Γ Δ extra : List Width} {saved carried result : Width}
variable {cfg : TargetCfg Input saved carried result extra full}

private theorem eval_select (code : Block TargetOp (ExitLabel bank full) Γ Δ) (env : Env Γ) :
    code.eval evalOp (fun term values => term.eval values) env =
      (code.eval evalOp select env).map Prod.snd id := by
  induction code with
  | terminator term =>
    cases term <;> simp [Silmaril.MLIR.Pure.Code.eval, Terminator.eval, select]
    split <;> rfl
  | letOp op operands _ ih => exact ih (.cons (evalOp op (operands.eval env)) env)

private theorem branch_no_return (code : Block TargetOp (ExitLabel bank full) Γ Δ)
    (branch : branches (terminal code).2 = true) (env : Env Γ) (out : Env Δ)
    (step : code.eval evalOp select env = .inr out) : False := by
  induction code with
  | terminator term =>
    cases term <;> simp [Silmaril.MLIR.Pure.Code.eval, terminal, branches, select] at branch step
    split at step <;> contradiction
  | letOp op operands _ ih => exact ih branch (.cons (evalOp op (operands.eval env)) env) step

private theorem runFrom_split (input : Env Input) (fuel : Nat)
    (branch : branches (terminal (cfg.block .header)).2 = true)
    (env : Env (SavedBank saved carried extra ++ Input)) :
    cfg.runBlock evalOp input fuel (cfg.block .header) env =
      (firstFrom? cfg input fuel env).bind
        (fun a => cfg.runFrom evalOp a.remaining input ⟨.exit, a.packet⟩) := by
  induction fuel generalizing env with
  | zero => rfl
  | succ fuel ih =>
    rw [Cfg.runBlock, eval_select, firstFrom?]
    cases step : (cfg.block .header).eval evalOp select env with
    | inr out => exact (branch_no_return _ branch env out step).elim
    | inl route =>
      obtain ⟨slot, label, packet⟩ := route
      cases label with
      | exit => rfl
      | header =>
        change cfg.runBlock evalOp input fuel (cfg.block .header) (packet.append input) =
          ((firstFrom? cfg input fuel (packet.append input)).map Arrival.bump).bind
            (fun a => cfg.runFrom evalOp a.remaining input ⟨.exit, a.packet⟩)
        rw [ih]
        cases firstFrom? cfg input fuel (packet.append input) <;> rfl

private theorem entry_checked (input : Env Input) (packet : Env (SavedBank saved carried extra))
    (found : entryPacket? cfg input = some packet) :
    cfg.entry.eval evalOp (fun term values => term.eval values) input = .inl ⟨.header, packet⟩ := by
  unfold entryPacket? at found
  split at found
  · rename_i _ step
    cases Option.some.inj found
    exact step
  · cases found

theorem run_split (input : Env Input) (fuel : Nat) (checked : admitted cfg input = true) :
    cfg.run evalOp fuel input =
      (firstExit? cfg input fuel).bind (fun a => cfg.runFrom evalOp a.remaining input ⟨.exit, a.packet⟩) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases found : entryPacket? cfg input with
    | none => simp [admitted, found] at checked
    | some packet =>
      have branch : branches (terminal (cfg.block .header)).2 = true := by
        simpa [admitted, found] using checked
      rw [Cfg.run, Cfg.runBlock, entry_checked input packet found, firstExit?, found]
      exact runFrom_split input fuel branch (packet.append input)

private theorem edge_project (p : Projection full) (edge : Edge (ExitLabel bank full) Γ) (env : Env Γ) :
    (p.edge edge).eval env = p.frame (edge.eval env) := by
  obtain ⟨label, args⟩ := edge
  cases label with
  | header => rfl
  | exit => simp only [Projection.edge, Edge.eval, Projection.frame, project_values]

private theorem term_project (p : Projection full)
    (term : Terminator (ExitLabel bank full) Δ Γ) (env : Env Γ) :
    select (p.term term) env = (select term env).map (fun (slot, frame) => (slot, p.frame frame)) id := by
  cases term <;> simp only [Projection.term, select, Sum.map, edge_project] <;> try rfl
  split <;> rfl

private theorem code_project (p : Projection full)
    (code : Block TargetOp (ExitLabel bank full) Γ Δ) (env : Env Γ) :
    (code.mapTerm p.term).eval evalOp select env =
      (code.eval evalOp select env).map (fun (slot, frame) => (slot, p.frame frame)) id := by
  induction code with
  | terminator term => exact term_project p term env
  | letOp op operands _ ih => exact ih (.cons (evalOp op (operands.eval env)) env)

private theorem entry_project (emission : Emission cfg) (input : Env Input) :
    entryPacket? emission.cfg input = entryPacket? cfg input := by
  unfold entryPacket? Emission.cfg
  rw [eval_select, code_project, eval_select]
  generalize cfg.entry.eval evalOp select input = step
  cases step with
  | inr => rfl
  | inl route =>
    obtain ⟨slot, label, packet⟩ := route
    cases label <;> rfl

private theorem from_project (emission : Emission cfg) (input : Env Input) (fuel : Nat)
    (env : Env (SavedBank saved carried extra ++ Input)) :
    firstFrom? emission.cfg input fuel env =
      (firstFrom? cfg input fuel env).map (·.project emission.projection) := by
  induction fuel generalizing env with
  | zero => rfl
  | succ fuel ih =>
    rw [firstFrom?, firstFrom?]
    have step := code_project emission.projection (cfg.block .header) env
    change (emission.cfg.block .header).eval evalOp select env = _ at step
    rw [step]
    cases (cfg.block .header).eval evalOp select env with
    | inr => rfl
    | inl route =>
      obtain ⟨slot, label, packet⟩ := route
      cases label with
      | exit => rfl
      | header =>
        change (firstFrom? emission.cfg input fuel (packet.append input)).map Arrival.bump =
          ((firstFrom? cfg input fuel (packet.append input)).map Arrival.bump).map (·.project emission.projection)
        rw [ih]
        cases firstFrom? cfg input fuel (packet.append input) <;> rfl

theorem first_project (emission : Emission cfg) (input : Env Input) (fuel : Nat) :
    firstExit? emission.cfg input fuel = (firstExit? cfg input fuel).map (·.project emission.projection) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [firstExit?, firstExit?, entry_project]
    cases entryPacket? cfg input with
    | none => rfl
    | some packet => exact from_project emission input fuel (packet.append input)

private theorem from_selected (input : Env Input) (fuel : Nat)
    (env : Env (SavedBank saved carried extra ++ Input))
    (a : Arrival Input (SavedBank saved carried extra) full) (found : firstFrom? cfg input fuel env = some a) :
    (cfg.block .header).eval evalOp select a.env = .inl (a.slot, ⟨.exit, a.packet⟩) ∧
      fuel = a.feedbacks + 1 + a.remaining := by
  induction fuel generalizing env a with
  | zero => cases found
  | succ fuel ih =>
    rw [firstFrom?] at found
    cases step : (cfg.block .header).eval evalOp select env with
    | inr => rw [step] at found; cases found
    | inl route =>
      obtain ⟨slot, label, packet⟩ := route
      rw [step] at found
      cases label with
      | exit =>
        cases Option.some.inj found
        exact ⟨step, by simp; omega⟩
      | header =>
        change (firstFrom? cfg input fuel (packet.append input)).map Arrival.bump = some a at found
        cases before : firstFrom? cfg input fuel (packet.append input) with
        | none => rw [before] at found; cases found
        | some next =>
          rw [before] at found
          cases Option.some.inj found
          obtain ⟨selected, count⟩ := ih _ _ before
          exact ⟨selected, by simp only [Arrival.bump]; omega⟩

theorem first_selected (input : Env Input) (fuel : Nat)
    (a : Arrival Input (SavedBank saved carried extra) full)
    (found : firstExit? cfg input fuel = some a) :
    (cfg.block .header).eval evalOp select a.env = .inl (a.slot, ⟨.exit, a.packet⟩) ∧
      fuel = a.feedbacks + 2 + a.remaining := by
  cases fuel with
  | zero => cases found
  | succ fuel =>
    rw [firstExit?] at found
    cases init : entryPacket? cfg input with
    | none => rw [init] at found; cases found
    | some packet =>
      rw [init] at found
      obtain ⟨selected, count⟩ := from_selected input fuel (packet.append input) a found
      exact ⟨selected, by omega⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run
