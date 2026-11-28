module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Execution
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.Recovery

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run

open Silmaril.MLIR.Arith (Atom Env Width)
open Silmaril.Isotope (Value)
open Loop.MLIR.CF (evalOp)

variable {Input full extra : List Width} {saved carried result : Width}
variable {cfg : TargetCfg Input saved carried result extra full}

/-- Split the actual bounded CF evaluator at the first taken exit edge.
For a checked entry, failure to arrive or to execute the exit exhausts
the same run budget. -/
theorem run_split (input : Env Input) (fuel : Nat) (checked : admitted cfg input = true) :
    cfg.run evalOp fuel input =
      (firstExit? cfg input fuel).bind (fun a => cfg.runFrom evalOp a.remaining input ⟨.exit, a.packet⟩) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.run_split input fuel checked

/-- The recovered slot was taken in the recovered environment. Fuel counts
one entry, all taken feedback steps, and the header step that enters exit. -/
theorem firstExit_selected (input : Env Input) (fuel : Nat)
    (a : Arrival Input (SavedBank saved carried extra) full) (found : firstExit? cfg input fuel = some a) :
    (cfg.block .header).eval evalOp select a.env = .inl (a.slot, ⟨.exit, a.packet⟩) ∧
      fuel = a.feedbacks + 2 + a.remaining :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.first_selected input fuel a found

/-- Full and compact bounded execution recover the same occurrence, header
environment, feedback count, and remaining CF fuel. The arriving packet
changes by precisely the emitter's typed projection. -/
theorem firstExit_project (emission : Emission cfg) (input : Env Input) (fuel : Nat) :
    firstExit? emission.cfg input fuel = (firstExit? cfg input fuel).map (·.project emission.projection) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.first_project emission input fuel

/-- A successful bounded run from checked entry provides the selected
explicit Φ row, projected latch, and the actual exit continuation. -/
theorem recover_of_run (emission : Emission cfg) (input : Env Input) (fuel : Nat) {output : Env [result]}
    (checked : admitted emission.cfg input = true) (returned : emission.cfg.run evalOp fuel input = some output) :
    Nonempty (Recovery emission input fuel output) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.recover emission input fuel checked returned

/-- Transferring the row discovered by the run yields exactly the projected
packet, with unchanged λSSA branch state. -/
theorem Recovery.transfer_iff {emission : Emission cfg} {input : Env Input} {fuel : Nat} {output : Env [result]}
    {σ : Type} (recovered : Recovery emission input fuel output)
    (instr : Silmaril.MLIR.Arith.Prim → Value Atom → σ → Value Atom → σ → Prop)
    (start finish : σ) (label : Nat) (payload : Value Atom) :
    Isotope.LambdaSSA.Semantics.Region.Eval instr
      (terminalEnv (emission.cfg.block .header) recovered.arrival.env).toLambdaSSA
      (.br recovered.row.edge.target recovered.row.edge.argument) start label payload finish ↔
    label = 0 ∧ payload = pack (emission.projection.values recovered.arrival.packet) ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run.transfer recovered instr start finish label payload

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Run
