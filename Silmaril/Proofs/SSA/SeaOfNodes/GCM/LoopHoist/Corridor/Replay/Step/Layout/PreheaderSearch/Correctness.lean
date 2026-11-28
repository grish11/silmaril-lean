module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch
open AfterReorder.Second (savedHeader)
open Header.Typed (edgePackets)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width} {origin cut headerBudget : Nat}
variable {state : Layout.State Input saved carried result extra} {moved : Layout.Move state}
variable {ranked : Ranked state origin}

private theorem mem_latest_cuts {index last : Nat} :
    index ∈ Layout.Discovery.Policy.latest.cuts last ↔ index ≤ last := by
  simp [Layout.Discovery.Policy.cuts, Nat.lt_succ_iff]

theorem latest?_some (selected : latest? state origin = some (cut, moved)) :
    cut ≤ state.savedCount ∧ Layout.emit? state ⟨origin, cut⟩ = some moved := by
  obtain ⟨index, listed, picked⟩ := List.exists_of_findSome?_eq_some selected
  obtain ⟨emitted, done, same⟩ := Option.map_eq_some_iff.mp picked
  cases same
  exact ⟨mem_latest_cuts.mp listed, done⟩

theorem latest?_none :
    latest? state origin = none ↔ ∀ cut ≤ state.savedCount, Layout.emit? state ⟨origin, cut⟩ = none := by
  simp only [latest?, List.findSome?_eq_none_iff, mem_latest_cuts, Option.map_eq_none_iff]

theorem latest?_max (selected : latest? state origin = some (cut, moved))
    {other : Nat} {alternative : Layout.Move state} (inRange : other ≤ state.savedCount)
    (accepted : Layout.emit? state ⟨origin, other⟩ = some alternative) : other ≤ cut := by
  obtain ⟨before, index, after, ordered, picked, rejected⟩ := List.findSome?_eq_some_iff.mp selected
  obtain ⟨emitted, _, same⟩ := Option.map_eq_some_iff.mp picked
  cases same
  have listed := mem_latest_cuts.mpr inRange
  rw [ordered] at listed
  have survives : other ∉ before := by
    intro earlier
    have failed := rejected other earlier
    simp [accepted] at failed
  rcases List.mem_cons.mp ((List.mem_append.mp listed).resolve_left survives) with equal | later
  · exact equal.le
  · have sorted : (Layout.Discovery.Policy.latest.cuts state.savedCount).Pairwise (fun a b => b ≤ a) :=
      List.pairwise_reverse.mpr List.pairwise_le_range
    rw [ordered] at sorted
    exact (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 _ later

theorem refuses_outOfRange (valid : Layout.Invariant state) (outside : state.savedCount < cut) :
    Layout.emit? state ⟨origin, cut⟩ = none := by
  cases emitted : Layout.emit? state ⟨origin, cut⟩ with
  | none => rfl
  | some moved =>
    have listed := (Layout.Discovery.mem_acceptedCuts_iff valid origin cut).mpr ⟨moved, emitted⟩
    have inRange := (List.mem_filter.mp listed).1
    simp [Layout.Discovery.Policy.cuts, Nat.lt_succ_iff, Nat.not_le_of_lt outside] at inRange

theorem refuses_unavailable {kept : Layout.CrossBlock.Kept (Label saved carried result extra)}
    {operand : Point (Label saved carried result extra)}
    (supported : Layout.Discovery.supported? state = true)
    (ready : Layout.CrossBlock.keep? state origin = some kept)
    (read : operand ∈ kept.sites.operands) (missing : ¬ operand.AvailableAt state.cfg ⟨none, cut⟩) :
    Layout.emit? state ⟨origin, cut⟩ = none := by
  cases emitted : Layout.emit? state ⟨origin, cut⟩ with
  | none => rfl
  | some moved =>
    have legal := (Layout.CrossBlock.emit?_sites supported ready emitted).2.2
    exact False.elim (missing (legal.operands_available _ read).2)

theorem refuses_before_definition {kept : Layout.CrossBlock.Kept (Label saved carried result extra)}
    {operand : Point (Label saved carried result extra)}
    (supported : Layout.Discovery.supported? state = true)
    (ready : Layout.CrossBlock.keep? state origin = some kept)
    (read : operand ∈ kept.sites.operands) (entrySite : operand.block = none) (early : cut < operand.cut) :
    Layout.emit? state ⟨origin, cut⟩ = none :=
  refuses_unavailable supported ready read fun available =>
    (Nat.not_le_of_lt early) (available.local_order entrySite)

theorem refuses_header_operand {kept : Layout.CrossBlock.Kept (Label saved carried result extra)}
    {operand : Point (Label saved carried result extra)}
    (supported : Layout.Discovery.supported? state = true)
    (ready : Layout.CrossBlock.keep? state origin = some kept)
    (read : operand ∈ kept.sites.operands) (headerSite : operand.block = savedHeader) :
    Layout.emit? state ⟨origin, cut⟩ = none := by
  apply refuses_unavailable supported ready read
  intro available
  have dominates := available.dominates
  rw [headerSite] at dominates
  have impossible := dominates [none] EntryPath.entry
  simp [savedHeader] at impossible

theorem rank?_spec (accepted : rank? state origin headerBudget = some ranked) :
    ranked.crossBlock.preheader = (latest? state origin).map Prod.snd := by
  have analyzed := (Layout.HeaderSplice.Walk.rank?_spec accepted).1
  rw [(Layout.CrossBlock.analyze?_spec analyzed).2.2.2.2]
  cases scanned : latest? state origin with
  | none =>
    simpa [nomination, scanned] using (latest?_none.mp scanned) 0 (Nat.zero_le _)
  | some candidate =>
    rcases candidate with ⟨cut, moved⟩
    simpa [nomination, scanned] using (latest?_some scanned).2

theorem rank?_sites (accepted : rank? state origin headerBudget = some ranked)
    (found : latest? state origin = some (cut, moved)) :
    moved.append.index = ranked.walked.start.binding.index ∧
    ranked.walked.start.binding.sites =
      ⟨(state.atLayout moved.append.candidate).operands, moved.append.candidate.uses⟩ ∧
    Legal state.cfg ranked.walked.start.binding.sites.operands ranked.walked.start.binding.sites.uses ⟨none, cut⟩ := by
  have walked := (Layout.HeaderSplice.Walk.rank?_spec accepted).2.1
  exact Layout.CrossBlock.emit?_sites (request := ⟨origin, cut⟩)
    (Layout.HeaderSplice.Walk.walk?_spec walked).1 ranked.walked.start.checked (latest?_some found).2

theorem rank?_hoist (accepted : rank? state origin headerBudget = some ranked)
    (chosen : ranked.crossBlock.selectedMove? = some moved) :
    ∃ cut, latest? state origin = some (cut, moved) ∧ ranked.selection.1 = ⟨none, cut⟩ ∧
      ranked.selection.2 = ⟨_, moved.next⟩ := by
  have preheader := chosen
  unfold Layout.CrossBlock.Analysis.selectedMove? at preheader
  split at preheader
  · rw [rank?_spec accepted] at preheader
    obtain ⟨⟨cut, move⟩, scanned, equal⟩ := Option.map_eq_some_iff.mp preheader
    cases equal
    have analyzed := (Layout.HeaderSplice.Walk.rank?_spec accepted).1
    have request := (Layout.CrossBlock.analyze?_spec analyzed).2.1
    refine ⟨cut, scanned, ?_, ?_⟩
    · simp [Layout.HeaderSplice.Walk.Ranked.selection, Layout.CrossBlock.Analysis.point, chosen, request,
        nomination, scanned]
    · simp [Layout.HeaderSplice.Walk.Ranked.selection, Layout.CrossBlock.Analysis.output, chosen]
  · cases preheader

theorem rank?_minDepth (accepted : rank? state origin headerBudget = some ranked) :
    ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth savedHeader ∧
    ∀ {other : Nat} {alternative : Layout.Move state}, other ≤ state.savedCount →
      Layout.emit? state ⟨origin, other⟩ = some alternative →
      ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth none := by
  have ordered := Layout.HeaderSplice.Walk.selected_minDepth ranked
  refine ⟨ordered.1, fun {other alternative} inRange emitted => ?_⟩
  apply ordered.2
  cases scanned : latest? state origin with
  | none => simp [(latest?_none.mp scanned) other inRange] at emitted
  | some candidate => simp [rank?_spec accepted, scanned]

theorem latest?_packets (selected : latest? state origin = some (cut, moved)) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    let value := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))
    Saved.StepRoutes state.cfg moved.next.cfg input values value ∧
    ∀ latch : BitVec carried.val,
      let source := (values.append (.cons latch .nil)).append input
      (moved.next.cfg.block .header).eval evalOp edgePackets (.cons value source) =
        ((state.cfg.block .header).eval evalOp edgePackets source).map
          (fun packet => (packet.1, Saved.prependFrame value packet.2)) := by
  have emitted := (latest?_some selected).2
  have append := Step.emit_spec (Layout.emit?_spec emitted).1
  exact ⟨Layout.emit?_routes valid emitted matched, fun latch =>
    AfterReorder.Second.Emit.emitAt?_edgePackets append.2.2.1 append.2.2.2.2.1 input values latch⟩

theorem rank?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state origin headerBudget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    ranked.selection.2.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Layout.HeaderSplice.Walk.rank?_run_eq accepted valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem rank?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state origin headerBudget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed ranked.selection.2.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input :=
  Layout.HeaderSplice.Walk.rank?_denotePart accepted valid prior matched

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch
