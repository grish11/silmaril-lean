module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Execution

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run

open Silmaril.MLIR.Arith (Atom Env Width)
open Silmaril.MLIR.CF (Block Terminator)
open Silmaril.Isotope (Value)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink (ExitLabel SavedBank TargetCfg)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Typed (edgePackets)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)

variable {Input bank full Γ Δ extra : List Width} {saved carried result : Width}
variable {cfg : TargetCfg Input saved carried result extra full}

private theorem term_observes (term : Terminator (ExitLabel bank full) Δ Γ) (env : Env Γ) :
    match select term env with
    | .inl (slot, frame) =>
      (edgePackets term env).findSome? (fun (actual, packet) => if actual = slot then exitValues? packet else none) =
        exitValues? frame
    | .inr _ => True := by
  cases term with
  | ret => trivial
  | br => simp [select, edgePackets]
  | condBr check yes no =>
    by_cases taken : (env.get check).getLsbD 0 = true
    · simp [select, taken, edgePackets, List.findSome?, reduceCtorEq]
      cases exitValues? (yes.eval env) <;> rfl
    · simp [select, taken, edgePackets, List.findSome?, reduceCtorEq]
      cases exitValues? (no.eval env) <;> rfl

private theorem code_observes (code : Block TargetOp (ExitLabel bank full) Γ Δ) (env : Env Γ) :
    match code.eval evalOp select env with
    | .inl (slot, frame) =>
      (code.eval evalOp edgePackets env).findSome?
        (fun (actual, packet) => if actual = slot then exitValues? packet else none) = exitValues? frame
    | .inr _ => True := by
  induction code with
  | terminator term => exact term_observes term env
  | letOp op operands _ ih => exact ih (.cons (evalOp op (operands.eval env)) env)

theorem first_packet (input : Env Input) (fuel : Nat) (a : Arrival Input (SavedBank saved carried extra) full)
    (found : firstExit? cfg input fuel = some a) :
    packetAt? cfg (.header, a.slot) a.env = some a.packet := by
  have observes := code_observes (cfg.block .header) a.env
  rw [(first_selected input fuel a found).1] at observes
  exact observes

theorem recover (emission : Emission cfg) (input : Env Input) (fuel : Nat) {output : Env [result]}
    (checked : admitted emission.cfg input = true) (returned : emission.cfg.run evalOp fuel input = some output) :
    Nonempty (Recovery emission input fuel output) := by
  have suffix := returned
  rw [run_split input fuel checked] at suffix
  cases found : firstExit? cfg input fuel with
  | none =>
    rw [first_project, found] at suffix
    cases suffix
  | some arrival =>
    have compactFound : firstExit? emission.cfg input fuel = some (arrival.project emission.projection) := by
      rw [first_project, found]
      rfl
    rw [compactFound] at suffix
    have fullPacket := first_packet input fuel arrival found
    have compactPacket :
        packetAt? emission.cfg (.header, arrival.slot) arrival.env = some (emission.projection.values arrival.packet) :=
      (packetAt_project emission (.header, arrival.slot) arrival.env).trans
        (congrArg (Option.map emission.projection.values) fullPacket)
    have latch :
        latchAt? emission.cfg (.header, arrival.slot) arrival.env = some (pack (emission.projection.values arrival.packet)) :=
      (latchAt_packet (.header, arrival.slot) arrival.env).trans (congrArg (Option.map pack) compactPacket)
    have present : (operandsAt? emission.cfg (.header, arrival.slot)).isSome = true := by
      by_contra absent
      simp [latchAt?, absent] at latch
    exact ⟨⟨arrival, found, compactFound, present, fullPacket, compactPacket, latch, suffix,
      (run_eq emission input fuel).symm.trans returned⟩⟩

theorem transfer {emission : Emission cfg} {input : Env Input} {fuel : Nat} {output : Env [result]}
    {σ : Type} (recovered : Recovery emission input fuel output)
    (instr : Silmaril.MLIR.Arith.Prim → Value Atom → σ → Value Atom → σ → Prop)
    (start finish : σ) (label : Nat) (payload : Value Atom) :
    Isotope.LambdaSSA.Semantics.Region.Eval instr
      (terminalEnv (emission.cfg.block .header) recovered.arrival.env).toLambdaSSA
      (.br recovered.row.edge.target recovered.row.edge.argument) start label payload finish ↔
    label = 0 ∧ payload = pack (emission.projection.values recovered.arrival.packet) ∧ finish = start := by
  have step := Incoming.transfer_iff recovered.row recovered.arrival.env instr start finish label payload
  simp only [Run.Recovery.row, predecessor, recovered.compactPacket, Option.map_some, Option.some.injEq] at step
  exact step.trans ⟨fun ⟨target, value, state⟩ => ⟨target, value.symm, state⟩,
    fun ⟨target, value, state⟩ => ⟨target, value.symm, state⟩⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run
