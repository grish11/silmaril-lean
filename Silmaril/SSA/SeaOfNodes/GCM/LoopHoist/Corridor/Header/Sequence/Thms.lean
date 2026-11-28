module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Earlier (Operation operations)
open Pair (Request)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {cfg out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {state next : State Input carried result} {request : Request} {requests : List Request}

/-- The origin-index splice uses exactly the typed emitter's order change. -/
theorem move?_transport (moved : Pair.move? cfg request = some out) :
    ∃ chosen : Operation,
      (operations (cfg.block .header))[request.binding]? = some chosen ∧
      operations (out.block .header) = relocate request chosen (operations (cfg.block .header)) ∧
      request.insertion < (operations (cfg.block .header)).length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.move?_transport moved

theorem initial_tracked (cfg : Cfg TargetOp (SourceLabel carried result) Input [result]) :
    Tracked (operations (cfg.block .header)) (initial cfg) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.initial_tracked cfg

/-- Every successful sequence preserves the origin permutation, its
alignment with the typed operation order, and distinct moved identities. -/
theorem run?_tracked {source : List Operation} (tracked : Tracked source state)
    (accepted : run? state requests = some next) : Tracked source next :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.run?_tracked tracked accepted

theorem run?_append (state : State Input carried result) (pre post : List Request) :
    run? state (pre ++ post) = (run? state pre).bind (fun next => run? next post) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.run?_append state pre post

/-- The checked sequence replaces only the header, preserving its evaluated frame. -/
theorem run?_header (accepted : run? state requests = some next) :
    ∃ header, next.cfg = withHeader state.cfg header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        (state.cfg.block .header).eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.run?_header accepted

/-- A failing suffix cannot return the successfully rewritten prefix. -/
theorem schedule?_refuses_suffix {pre post : List Request}
    (ran : run? (initial (lower g)) pre = some state) (rejected : run? state post = none) :
    schedule? g (pre ++ post) = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.schedule?_refuses_suffix ran rejected

/-- The full sequence preserves entry, feedback, and exit observations. -/
theorem schedule?_frames (accepted : schedule? g requests = some out) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.schedule?_frames accepted input

theorem schedule?_run_eq (accepted : schedule? g requests = some out) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.schedule?_run_eq accepted input fuel

theorem schedule?_budget (accepted : schedule? g requests = some out) (input : Env Input)
    (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.schedule?_budget accepted input budget

theorem schedule?_denotePart (accepted : schedule? g requests = some out) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.schedule?_denotePart accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence
