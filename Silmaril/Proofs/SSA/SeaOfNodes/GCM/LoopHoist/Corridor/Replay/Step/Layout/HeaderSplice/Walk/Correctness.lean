module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk
open AfterReorder.Second (savedHeader)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width} {origin budget : Nat}
variable {source : Position Input saved carried result extra origin}

private theorem step_binding (step : Step source) : step.move.binding = source.2.binding :=
  Option.some.inj ((Layout.HeaderSplice.emit?_spec step.emitted).2.1.symm.trans source.2.checked)

theorem step_cut (step : Step source) :
    step.move.cut = ⟨savedHeader, source.index + 2⟩ ∧
    step.move.insertion = step.target.index ∧
    Legal source.1.cfg source.2.binding.sites.operands source.2.binding.sites.uses step.move.cut := by
  have spec := Layout.HeaderSplice.emit?_spec step.emitted
  refine ⟨by simp only [Layout.HeaderSplice.Move.cut, spec.1], ?_, ?_⟩
  · unfold Layout.HeaderSplice.Move.insertion
    rw [spec.1, step_binding step]
    change Header.afterRemoval source.index (source.index + 2) = step.next.binding.index
    rw [step.advanced]
    simp [Header.afterRemoval]
  · simpa only [step_binding step] using spec.2.2.2.1

theorem step_sites (step : Step source) : step.target.2.binding.sites = source.2.binding.sites := by
  have scanned := (Layout.CrossBlock.keep?_spec step.next.checked).2.1
  change Layout.CrossBlock.findSites? step.move.next step.target.index 0 (Saved.origins (extra ++ [saved]))
    (step.move.next.cfg.block .header) = some step.next.binding.sites at scanned
  rw [← (step_cut step).2.1] at scanned
  have same := Option.some.inj (scanned.symm.trans (Layout.HeaderSplice.emit?_spec step.emitted).2.2.2.2.2)
  exact same.trans (congrArg Layout.CrossBlock.Kept.sites (step_binding step))

private theorem trace_first (trace : Trace source) : source ∈ trace.positions := by
  cases trace <;> simp [Trace.positions]

theorem trace_latest (trace : Trace source) :
    trace.last ∈ trace.positions ∧
      ∀ candidate ∈ trace.positions, candidate.index ≤ trace.last.index := by
  induction trace with
  | halt => simp [Trace.positions, Trace.last]
  | step first rest ih =>
    refine ⟨List.mem_cons_of_mem _ ih.1, ?_⟩
    intro candidate member
    rcases List.mem_cons.mp member with rfl | tail
    · have after := ih.2 _ (trace_first rest)
      change first.target.index ≤ rest.last.index at after
      have advanced : first.target.index = _ := first.advanced
      exact Nat.le_trans (by omega) after
    · exact ih.2 _ tail

theorem visit_bound (source : Position Input saved carried result extra origin) (budget : Nat) :
    (visit source budget).positions.length ≤ budget + 1 := by
  induction budget generalizing source with
  | zero => simp [visit, Trace.positions]
  | succ budget ih =>
    rw [visit]
    split
    · simp [Trace.positions]
    · rename_i first _
      exact Nat.succ_le_succ (ih first.target)

theorem trace_blocked (trace : Trace source) (blocked : trace.blocked = true) : step? trace.last = none := by
  cases stopped : trace.stop with
  | limit => simp [Trace.blocked, stopped] at blocked
  | blocked checked => exact checked

theorem trace_sites (trace : Trace source) {candidate : Position Input saved carried result extra origin}
    (member : candidate ∈ trace.positions) : candidate.2.binding.sites = source.2.binding.sites := by
  induction trace with
  | halt =>
    have same := List.mem_singleton.mp member
    cases same
    rfl
  | step first rest ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · rfl
    · exact (ih tail).trans (step_sites first)

theorem trace_frames (trace : Trace source) (input : Env Input) :
    trace.last.1.cfg.entry = source.1.cfg.entry ∧
    trace.last.1.cfg.block .exit = source.1.cfg.block .exit ∧
    ∀ frame : Frame (Label saved carried result extra),
      (trace.last.1.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        (source.1.cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  induction trace with
  | halt => exact ⟨rfl, rfl, fun _ => rfl⟩
  | step first _ ih =>
    obtain ⟨entry, exit, transfer⟩ := Layout.HeaderSplice.emit?_frames first.emitted input
    exact ⟨ih.1.trans entry, ih.2.1.trans exit, fun frame => (ih.2.2 frame).trans (transfer frame)⟩

theorem trace_edgePackets (trace : Trace source) (env : Env (((extra ++ [saved]) ++ [carried]) ++ Input)) :
    (trace.last.1.cfg.block .header).eval evalOp Header.Typed.edgePackets env =
      (source.1.cfg.block .header).eval evalOp Header.Typed.edgePackets env := by
  induction trace with
  | halt => rfl
  | step first _ ih => exact ih.trans (Layout.HeaderSplice.emit?_edgePackets first.emitted env)

theorem trace_routes {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])} (trace : Trace source)
    (prior : RoutesWith base source.1.cfg input values) : RoutesWith base trace.last.1.cfg input values := by
  induction trace with
  | halt => exact prior
  | step first _ ih => exact ih (Layout.HeaderSplice.emit?_routes first.emitted prior)

theorem trace_invariant (trace : Trace source) (valid : Layout.Invariant source.1) :
    Layout.Invariant trace.last.1 := by
  induction trace with
  | halt => exact valid
  | step first _ ih => exact ih (Layout.HeaderSplice.next_invariant (move := first.move) valid)

theorem trace_run_eq (trace : Trace source) (input : Env Input) (fuel : Nat) :
    trace.last.1.cfg.run evalOp fuel input = source.1.cfg.run evalOp fuel input :=
  let ⟨entry, _, frames⟩ := trace_frames trace input
  Header.Typed.run_eq_of_frames input entry frames fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem trace_denotePart (trace : Trace source) (input : Env Input) :
    (Cfg.embed trace.last.1.cfg).denotePart evalOp input = (Cfg.embed source.1.cfg).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, trace_run_eq trace]

variable {state : Layout.State Input saved carried result extra} {request : Nomination}
theorem walk?_spec {walked : Layout.HeaderSplice.Walk.Walk state origin} (accepted : walk? state origin budget = some walked) :
    Layout.Discovery.supported? state = true ∧ walked.trace = visit ⟨state, walked.start⟩ budget := by
  cases supported : Layout.Discovery.supported? state with
  | false => simp [walk?, supported] at accepted
  | true =>
    simp only [walk?, supported, ↓reduceIte] at accepted
    obtain ⟨start, _, same⟩ := Option.bind_eq_some_iff.mp accepted
    cases same
    exact ⟨rfl, rfl⟩

variable {ranked : Ranked state request}

theorem rank?_spec (accepted : rank? state request budget = some ranked) :
    Layout.CrossBlock.analyze? state request = some ranked.crossBlock ∧
    walk? state request.origin budget = some ranked.walked ∧
    ranked.walked.start.binding = ranked.crossBlock.kept := by
  obtain ⟨outside, analyzed, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨inside, walked, same⟩ := Option.bind_eq_some_iff.mp rest
  cases same
  have kept := (Layout.CrossBlock.analyze?_spec analyzed).2.2.1
  exact ⟨analyzed, walked, Option.some.inj (inside.start.checked.symm.trans kept)⟩

theorem selected_minDepth (ranked : Ranked state request) :
    ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth savedHeader ∧
    (ranked.crossBlock.preheader.isSome →
      ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth none) := by
  have same : ranked.selection.1.block = ranked.crossBlock.point.block := by
    cases outside : ranked.crossBlock.selectedMove?.isSome <;>
      simp [Ranked.selection, outside, Layout.CrossBlock.Analysis.point, Layout.CrossBlock.Kept.point]
  rw [same]
  exact ⟨(Layout.CrossBlock.selected_minDepth ranked.crossBlock).1,
    (Layout.CrossBlock.selected_minDepth ranked.crossBlock).2.1⟩

theorem selected_latest (ranked : Ranked state request) (inside : ranked.crossBlock.selectedMove?.isSome = false) :
    ranked.selection.1 = ⟨savedHeader, ranked.walked.trace.last.index⟩ ∧
    ranked.selection.2 = ⟨extra, ranked.walked.trace.last.1⟩ ∧
    ranked.walked.trace.last ∈ ranked.walked.trace.positions ∧
    ∀ candidate ∈ ranked.walked.trace.positions, candidate.index ≤ ranked.selection.1.cut := by
  simpa [Ranked.selection, inside] using trace_latest ranked.walked.trace

theorem rank?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request budget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    ranked.selection.2.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input := by
  have analyzed := (rank?_spec accepted).1
  unfold Ranked.selection
  cases outside : ranked.crossBlock.selectedMove?.isSome
  · exact trace_run_eq ranked.walked.trace input fuel
  · exact Layout.CrossBlock.analyze?_run_eq analyzed valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem rank?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state request budget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed ranked.selection.2.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, rank?_run_eq accepted valid prior matched]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk
