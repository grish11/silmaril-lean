module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open AfterReorder.Second (savedHeader)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width} {origin budget : Nat}
variable {source : Position Input saved carried result extra origin}

/-- Each step uses a legal cut in the current CFG and translates it to the checked position in the emitted CFG. -/
theorem step_cut (step : Step source) :
    step.move.cut = ⟨savedHeader, source.index + 2⟩ ∧
    step.move.insertion = step.target.index ∧
    Legal source.1.cfg source.2.binding.sites.operands source.2.binding.sites.uses step.move.cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.step_cut step

/-- The current and emitted positions have identical operand sites and exact use occurrences. -/
theorem step_sites (step : Step source) : step.target.2.binding.sites = source.2.binding.sites :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.step_sites step

/-- The last position was visited and has the largest index among the visited positions. -/
theorem trace_latest (trace : Trace source) :
    trace.last ∈ trace.positions ∧
      ∀ candidate ∈ trace.positions, candidate.index ≤ trace.last.index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_latest trace

/-- The visit list contains the start and at most one emitted position per unit of budget. -/
theorem visit_bound (source : Position Input saved carried result extra origin) (budget : Nat) :
    (visit source budget).positions.length ≤ budget + 1 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.visit_bound source budget

/-- A blocked trace certifies that the next checked step is refused at its final position. -/
theorem trace_blocked (trace : Trace source) (blocked : trace.blocked = true) : step? trace.last = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_blocked trace blocked

/-- Every visited position retains the initial operand sites, ordinary reads, and exact incoming Φ occurrences. -/
theorem trace_sites (trace : Trace source) {candidate : Position Input saved carried result extra origin}
    (member : candidate ∈ trace.positions) : candidate.2.binding.sites = source.2.binding.sites :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_sites trace member

/-- Entry and exit stay syntactically equal, and each frame yields the same transfer. -/
theorem trace_frames (trace : Trace source) (input : Env Input) :
    trace.last.1.cfg.entry = source.1.cfg.entry ∧
    trace.last.1.cfg.block .exit = source.1.cfg.block .exit ∧
    ∀ frame : Frame (Label saved carried result extra),
      (trace.last.1.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        (source.1.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_frames trace input

/-- Both branch packets retain their slot and arguments, including the untaken edge. -/
theorem trace_edgePackets (trace : Trace source) (env : Env (((extra ++ [saved]) ++ [carried]) ++ Input)) :
    (trace.last.1.cfg.block .header).eval evalOp Header.Typed.edgePackets env =
      (source.1.cfg.block .header).eval evalOp Header.Typed.edgePackets env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_edgePackets trace env

/-- The walk transports the existing saved-packet routing invariant. -/
theorem trace_routes {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])} (trace : Trace source)
    (prior : RoutesWith base source.1.cfg input values) : RoutesWith base trace.last.1.cfg input values :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_routes trace prior

/-- The physical prefix and append reference still satisfy the layout invariant. -/
theorem trace_invariant (trace : Trace source) (valid : Layout.Invariant source.1) :
    Layout.Invariant trace.last.1 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_invariant trace valid

/-- Returns and exhaustion agree at each common CFG fuel. -/
theorem trace_run_eq (trace : Trace source) (input : Env Input) (fuel : Nat) :
    trace.last.1.cfg.run evalOp fuel input = source.1.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_run_eq trace input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The walked CFG has the same partial denotation. -/
theorem trace_denotePart (trace : Trace source) (input : Env Input) :
    (Cfg.embed trace.last.1.cfg).denotePart evalOp input = (Cfg.embed source.1.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.trace_denotePart trace input

variable {state : Layout.State Input saved carried result extra} {request : Nomination}

/-- The public entry point returns the exact bounded walk on the checked layout. -/
theorem walk?_spec {walked : Walk state origin} (accepted : walk? state origin budget = some walked) :
    Layout.Discovery.supported? state = true ∧ walked.trace = visit ⟨state, walked.start⟩ budget :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.walk?_spec accepted

variable {ranked : Ranked state request}

/-- Both analyses resolve the same live binding in the input CFG. -/
theorem rank?_spec (accepted : rank? state request budget = some ranked) :
    CrossBlock.analyze? state request = some ranked.crossBlock ∧
    walk? state request.origin budget = some ranked.walked ∧
    ranked.walked.start.binding = ranked.crossBlock.kept :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.rank?_spec accepted

/-- The selected block has minimum certified depth over the admitted preheader and visited header positions. -/
theorem selected_minDepth (ranked : Ranked state request) :
    ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth savedHeader ∧
    (ranked.crossBlock.preheader.isSome →
      ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth none) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.selected_minDepth ranked

/-- When depth selection stays in the header, the emitted latest visit wins. -/
theorem selected_latest (ranked : Ranked state request) (inside : ranked.crossBlock.selectedMove?.isSome = false) :
    ranked.selection.1 = ⟨savedHeader, ranked.walked.trace.last.index⟩ ∧
    ranked.selection.2 = ⟨extra, ranked.walked.trace.last.1⟩ ∧
    ranked.walked.trace.last ∈ ranked.walked.trace.positions ∧
    ∀ candidate ∈ ranked.walked.trace.positions, candidate.index ≤ ranked.selection.1.cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.selected_latest ranked inside

/-- Either selected CFG preserves the finite observations of the input layout. -/
theorem rank?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request budget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    ranked.selection.2.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.rank?_run_eq accepted valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The selected CFG preserves partial denotation under the existing saved-layout assumptions. -/
theorem rank?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request budget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed ranked.selection.2.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.rank?_denotePart accepted valid prior matched

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk
