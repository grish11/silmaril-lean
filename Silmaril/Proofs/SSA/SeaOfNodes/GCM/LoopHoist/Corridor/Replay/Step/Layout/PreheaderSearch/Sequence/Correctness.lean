module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence
open Layout.HeaderSplice.Walk (Position)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width} {origin : Nat}
variable {source : Layout.Output Input saved carried result} {request : Request} {rest requests : List Request}

private theorem walk_step_origins {position : Position Input saved carried result extra origin}
    (hop : Layout.HeaderSplice.Walk.Step position) :
    hop.target.1.reference.origins.Perm position.1.reference.origins := by
  let moved := hop.move
  have checked := Layout.HeaderSplice.emit?_spec hop.emitted
  have requested : moved.request.origin = origin := congrArg Nomination.origin checked.1
  have atSource := (Layout.CrossBlock.keep?_spec checked.2.1).1
  obtain ⟨bound, found, _⟩ := List.idxOf?_eq_some_iff.mp atSource
  have selected : position.1.reference.origins[moved.binding.index]? = some moved.request.origin := by
    rw [requested]
    exact List.getElem?_eq_some_iff.mpr ⟨bound, found⟩
  have atTarget := (Layout.CrossBlock.keep?_spec hop.next.checked).1
  have targetBound := (List.idxOf?_eq_some_iff.mp atTarget).1
  have inserted : moved.insertion = hop.next.binding.index := (Layout.HeaderSplice.Walk.step_cut hop).2.1
  rw [← inserted] at targetBound
  let erased := position.1.reference.origins.eraseIdx moved.binding.index
  change moved.insertion < (erased.insertIdx moved.insertion moved.request.origin).length at targetBound
  have inRange : moved.insertion ≤ erased.length := by
    by_contra outside
    rw [List.length_insertIdx_of_length_lt (Nat.lt_of_not_ge outside)] at targetBound
    omega
  have restored : (moved.request.origin :: erased).Perm position.1.reference.origins := by
    simpa only [Saved.Slots.origins, List.nil_append, List.cons_append] using
      Saved.promote_perm (w := saved) .nil selected
  exact (List.perm_insertIdx _ _ inRange).trans restored

private theorem walk_reference {position : Position Input saved carried result extra origin}
    (trace : Layout.HeaderSplice.Walk.Trace position) :
    trace.last.1.reference.cfg.entry = position.1.reference.cfg.entry ∧
    trace.last.1.reference.slots = position.1.reference.slots ∧
    trace.last.1.reference.origins.Perm position.1.reference.origins := by
  induction trace with
  | halt => exact ⟨rfl, rfl, .refl _⟩
  | step hop _ ih => exact ⟨ih.1.trans rfl, ih.2.1.trans rfl, ih.2.2.trans (walk_step_origins hop)⟩

theorem run_continue (choice : Choice source request) (position : Nat) :
    run source position (request :: rest) =
      (run choice.ranked.selection.2 (position + 1) rest).map (.step choice) := by
  rw [Layout.PreheaderSearch.Sequence.run]
  split
  · rename_i refused
    rw [choice.checked] at refused
    cases refused
  · rename_i ranked accepted
    have same := Option.some.inj (accepted.symm.trans choice.checked)
    subst ranked
    rfl

theorem run_refuses_current (refused : Layout.PreheaderSearch.rank? source.2 request.origin request.headerBudget = none)
    (position : Nat) :
    run source position (request :: rest) = .error ⟨position, request⟩ := by
  rw [Layout.PreheaderSearch.Sequence.run]
  split
  · rfl
  · rename_i ranked accepted
    rw [refused] at accepted
    cases accepted

variable {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {inventory : List Nat} {input : Env Input} {values : Env (source.1 ++ [saved])}

theorem choice_preserves (choice : Choice source request) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    let out := choice.ranked.selection.2
    Layout.Invariant out.2 ∧
    ∃ nextValues : Env (out.1 ++ [saved]),
      Saved.Invariant base out.2.cfg inventory out.2.reference.origins out.2.reference.slots input nextValues ∧
      Saved.Prefix.Matches out.2.reference.cfg.entry input nextValues := by
  dsimp only
  cases hoisted : choice.ranked.crossBlock.selectedMove? with
  | none =>
    have inside := Layout.HeaderSplice.Walk.selected_latest choice.ranked (by simp [hoisted])
    rw [inside.2.1]
    let trace := choice.ranked.walked.trace
    obtain ⟨entry, slots, origins⟩ := walk_reference trace
    refine ⟨Layout.HeaderSplice.Walk.trace_invariant trace valid, values, ⟨?_, ?_⟩, ?_⟩
    · rw [slots]
      exact (origins.append_left _).trans prior.partition
    · exact Layout.HeaderSplice.Walk.trace_routes trace prior.routes
    · exact entry.symm ▸ matched
  | some moved =>
    obtain ⟨cut, latest, _, out⟩ := Layout.PreheaderSearch.rank?_hoist choice.checked hoisted
    have emitted := (Layout.PreheaderSearch.latest?_some latest).2
    have append := Step.emit_spec (Layout.emit?_spec emitted).1
    have packets := (Layout.PreheaderSearch.latest?_packets latest valid matched).1
    have nextMatched := (AfterReorder.Second.Emit.emitAt?_step matched append.2.2.1 append.2.2.2.2.1).2
    rw [out]
    refine ⟨Layout.emit?_invariant valid emitted, _, ?_, nextMatched⟩
    change Saved.Invariant base moved.next.cfg inventory moved.append.next.origins
      moved.append.next.slots input _
    rw [append.2.2.2.2.2.1, append.2.2.2.2.2.2]
    exact prior.extend append.2.1 packets

theorem trace_preserves (trace : Trace source requests) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    let out := trace.output
    Layout.Invariant out.2 ∧
    ∃ finalValues : Env (out.1 ++ [saved]),
      Saved.Invariant base out.2.cfg inventory out.2.reference.origins out.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches out.2.reference.cfg.entry input finalValues := by
  induction trace with
  | done => exact ⟨valid, values, prior, matched⟩
  | step first _ ih =>
    obtain ⟨nextValid, _, nextPrior, nextMatched⟩ := choice_preserves first valid prior matched
    exact ih nextValid nextPrior nextMatched

theorem trace_run_eq (trace : Trace source requests) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) (fuel : Nat) :
    trace.output.2.cfg.run evalOp fuel input = source.2.cfg.run evalOp fuel input := by
  obtain ⟨_, _, final, _⟩ := trace_preserves trace valid prior matched
  exact (routesWith_run_eq final.routes fuel).trans (routesWith_run_eq prior.routes fuel).symm

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem trace_denotePart (trace : Trace source requests) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    (Cfg.embed trace.output.2.cfg).denotePart evalOp input = (Cfg.embed source.2.cfg).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, trace_run_eq trace valid prior matched]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence
