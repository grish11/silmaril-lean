module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Correctness
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery

open Silmaril.MLIR.Arith (Env Width)
open Header.Earlier (Operation operations)
open Loop.MLIR.CF (Program evalOp lower model)

variable {Input extra : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {state : Step.State Input saved carried result extra}
variable {g : Program Input carried result entrySigs headerSigs}
variable {header : List Header.Pair.Request} {plan : Plan Input carried result}

theorem choose?_spec {α : Type} {origins : List Nat} {cut : Nat} {tryMove : Nomination → Except Reason α}
    {request : Nomination} {out : α} (chosen : choose? origins cut tryMove = some (request, out)) :
    request.origin ∈ origins ∧ request.cut = cut ∧ tryMove request = .ok out :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.choose?_spec chosen

theorem laterMove?_none :
    laterMove? state = none ↔ ∀ request, ∃ reason, Step.emit state request = .error reason :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.laterMove?_none

theorem next?_none_iff (out : Step.Result Input carried result) :
    next? out = none ↔ Exhausted out :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.next?_none_iff out

theorem collect_replay (budget position : Nat) :
    Step.run state position (collect state budget).requests = .ok (collect state budget).output :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.collect_replay budget position

/-- Each admitted move removes one current header identity. -/
theorem collect_count (budget : Nat) :
    (collect state budget).output.2.origins.length + (collect state budget).requests.length =
      state.origins.length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.collect_count budget

theorem collect_exhausted {budget : Nat} (enough : state.origins.length ≤ budget) :
    laterMove? (collect state budget).output.2 = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.collect_exhausted enough

/-- Every surviving origin stays aligned with the emitted typed header. -/
theorem collect_origins {original : List Operation} (budget : Nat)
    (aligned : state.origins.map (fun origin => original[origin]?) = (operations (state.cfg.block .header)).map some) :
    (collect state budget).output.2.origins.map (fun origin => original[origin]?) =
      (operations ((collect state budget).output.2.cfg.block .header)).map some :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.collect_origins budget aligned

/-- Discovery returns the exact checked replay and stops only when no
nomination is eligible on the terminal CFG in its current phase. -/
theorem discover_spec (accepted : discover g header = .ok plan) :
    Step.replayAll g header plan.requests = .ok plan.output ∧ Exhausted plan.output ∧
      plan.output.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
        (headerOperations plan.output).map some :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.discover_spec accepted

theorem discover_run_eq (accepted : discover g header = .ok plan) (input : Env Input) (fuel : Nat) :
    plan.output.cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Step.replayAll_run_eq (discover_spec accepted).1 input fuel

theorem discover_budget (accepted : discover g header = .ok plan) (input : Env Input) (budget : Nat) :
    plan.output.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Step.replayAll_budget (discover_spec accepted).1 input budget

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem discover_denotePart (accepted : discover g header = .ok plan) (input : Env Input) :
    (Cfg.embed plan.output.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input :=
  Step.replayAll_denotePart (discover_spec accepted).1 input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery
