module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input : List Width} {saved carried result : Width}
variable {source : Layout.Output Input saved carried result} {request : Request} {rest requests : List Request}

/-- The tail is ranked from the exact selected layout of the first request. -/
theorem run_continue (choice : Choice source request) (position : Nat) :
    run source position (request :: rest) =
      (run choice.ranked.selection.2 (position + 1) rest).map (.step choice) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.run_continue choice position

/-- A refused current rank reports that request and position. -/
theorem run_refuses_current (refused : PreheaderSearch.rank? source.2 request.origin request.headerBudget = none)
    (position : Nat) :
    run source position (request :: rest) = .error ⟨position, request⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.run_refuses_current refused position

variable {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {inventory : List Nat} {input : Env Input} {values : Env (source.1 ++ [saved])}

/-- A checked choice transports the physical layout, full identity inventory,
    saved packets and matched append prefix to its selected CFG. -/
theorem choice_preserves (choice : Choice source request) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    let out := choice.ranked.selection.2
    Layout.Invariant out.2 ∧
    ∃ nextValues : Env (out.1 ++ [saved]),
      Saved.Invariant base out.2.cfg inventory out.2.reference.origins out.2.reference.slots input nextValues ∧
      Saved.Prefix.Matches out.2.reference.cfg.entry input nextValues :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.choice_preserves choice valid prior matched

/-- The three initial invariants suffice for every later rank in the trace,
    including layouts whose saved packet has grown. -/
theorem trace_preserves (trace : Trace source requests) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    let out := trace.output
    Layout.Invariant out.2 ∧
    ∃ finalValues : Env (out.1 ++ [saved]),
      Saved.Invariant base out.2.cfg inventory out.2.reference.origins out.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches out.2.reference.cfg.entry input finalValues :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.trace_preserves trace valid prior matched

/-- The exact selected layouts preserve return and exhaustion at each common fuel. -/
theorem trace_run_eq (trace : Trace source requests) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) (fuel : Nat) :
    trace.output.2.cfg.run evalOp fuel input = source.2.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.trace_run_eq trace valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The final and initial CFGs have the same partial observations. -/
theorem trace_denotePart (trace : Trace source requests) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    (Cfg.embed trace.output.2.cfg).denotePart evalOp input = (Cfg.embed source.2.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.trace_denotePart trace valid prior matched

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence
