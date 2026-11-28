module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Earlier (operations)
open Pair (Request)
open Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {state next : State Input carried result}
variable {out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {index origin : Nat} {request : Request} {requests : List Request} {priorities : List Nat}

/-- A resolved current position carries the requested original identity. -/
theorem resolve?_sound (resolved : resolve? state origin = some index) :
    state.origins[index]? = some origin :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.resolve?_sound resolved

/-- The selected cut is the smallest strictly earlier cut accepted by the
existing checked step for this binding and state. -/
theorem choose?_earliest (found : choose? state index = some (request, next)) :
    request.binding = index ∧ request.cut < index ∧ Sequence.step? state request = some next ∧
      ∀ cut < request.cut, Sequence.step? state ⟨index, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.choose?_earliest found

theorem choose?_eq_none : choose? state index = none ↔
    ∀ cut < index, Sequence.step? state ⟨index, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.choose?_eq_none

/-- Valid distinct priorities always produce a result, possibly an empty plan. -/
theorem schedule?_exists (distinct : priorities.Nodup)
    (known : ∀ origin ∈ priorities, origin < (operations ((lower g).block .header)).length) :
    ∃ requests out, schedule? g priorities = some (requests, out) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.schedule?_exists distinct known

/-- Replaying a plan reconstructs the whole tracked state, including origins. -/
theorem plan?_replay (planned : plan? state priorities = some (requests, next)) :
    Sequence.run? state requests = some next :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.plan?_replay planned

/-- Replay through the explicit sequence API gives exactly the returned CFG. -/
theorem schedule?_replay (accepted : schedule? g priorities = some (requests, out)) :
    Sequence.schedule? g requests = some out :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.schedule?_replay accepted

theorem schedule?_frames (accepted : schedule? g priorities = some (requests, out)) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.schedule?_frames accepted input

theorem schedule?_run_eq (accepted : schedule? g priorities = some (requests, out)) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.schedule?_run_eq accepted input fuel

theorem schedule?_budget (accepted : schedule? g priorities = some (requests, out))
    (input : Env Input) (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.schedule?_budget accepted input budget

theorem schedule?_denotePart (accepted : schedule? g priorities = some (requests, out)) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.schedule?_denotePart accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority
