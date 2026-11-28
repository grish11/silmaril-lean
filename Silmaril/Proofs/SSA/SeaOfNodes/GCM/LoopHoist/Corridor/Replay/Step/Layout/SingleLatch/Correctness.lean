module

import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch

open Silmaril.MLIR.Arith (Var Width)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
open AfterReorder.Second (intermediateBlocks savedHeader targetDecEqWith)
open AfterReorder.Second.Emit (emitAt? liftTarget liftCode rewriteAt?)
open NaturalLoop (Backedge)
open PreheaderSearch.Sequence.Discovery (Hoist hoist? choose? Plan schedule?)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra}

private theorem target_mem (target : Target (Label saved carried result extra)) :
    target ∈ (intermediateBlocks : List (Target (Label saved carried result extra))) := by
  rcases target with ⟨_, label⟩
  cases label <;> simp [intermediateBlocks]

private theorem vertices_mem (block : BlockId (Label saved carried result extra)) :
    block ∈ NaturalLoop.vertices intermediateBlocks := by
  cases block with
  | none => simp [NaturalLoop.vertices]
  | some target => simpa [NaturalLoop.vertices] using target_mem target

private def shapeCheck (entry yes no : BlockId (Label saved carried result extra))
    (exitCode : Block TargetOp (Label saved carried result extra) ([result] ++ Input) [result]) : Bool :=
  match entry, yes, no, exitCode with
  | some ⟨_, .header⟩, some ⟨_, .header⟩, some ⟨_, .exit⟩, .terminator (.ret _)
  | some ⟨_, .header⟩, some ⟨_, .exit⟩, some ⟨_, .header⟩, .terminator (.ret _) => true
  | _, _, _, _ => false

private theorem supported_eq (state : Layout.State Input saved carried result extra) :
    Discovery.supported? state =
      (decide (state.reference.origins.length = (shape state.cfg savedHeader).bindings ∧
        state.reference.origins.Nodup) &&
      shapeCheck ((shape state.cfg none).target .jump)
        ((shape state.cfg savedHeader).target .onTrue) ((shape state.cfg savedHeader).target .onFalse)
        (state.cfg.block .exit)) := rfl

private theorem checkedEdges
    {entry yes no : BlockId (Label saved carried result extra)}
    {exitCode : Block TargetOp (Label saved carried result extra) ([result] ++ Input) [result]}
    (checked : shapeCheck entry yes no exitCode = true) :
    entry = savedHeader ∧
    (yes = savedHeader ∧ no = some ⟨_, .exit⟩ ∨ yes = some ⟨_, .exit⟩ ∧ no = savedHeader) ∧
    ∀ slot, (shape.ofBlock exitCode).target slot = none := by
  rcases entry with _ | ⟨_, entryLabel⟩
  · exact Bool.noConfusion checked
  cases entryLabel
  case exit => exact Bool.noConfusion checked
  rcases yes with _ | ⟨_, yesLabel⟩
  · exact Bool.noConfusion checked
  rcases no with _ | ⟨_, noLabel⟩
  · cases yesLabel <;> exact Bool.noConfusion checked
  cases yesLabel <;> cases noLabel <;> try exact Bool.noConfusion checked
  all_goals
    cases exitCode with
    | letOp => exact Bool.noConfusion checked
    | terminator term =>
      cases term <;> try exact Bool.noConfusion checked
      first
      | exact ⟨rfl, .inl ⟨rfl, rfl⟩, fun slot => by cases slot <;> rfl⟩
      | exact ⟨rfl, .inr ⟨rfl, rfl⟩, fun slot => by cases slot <;> rfl⟩

private theorem edges (supported : Discovery.supported? state = true) :
    (shape state.cfg none).target .jump = savedHeader ∧
    (∃ slot, (shape state.cfg savedHeader).target slot = savedHeader) ∧
    (∃ slot, (shape state.cfg savedHeader).target slot = some ⟨_, .exit⟩) ∧
    ∀ slot, (shape state.cfg (some ⟨_, .exit⟩)).target slot = none := by
  have checked := (Bool.and_eq_true_iff.mp ((supported_eq _).symm.trans supported)).2
  obtain ⟨entry, arms, returns⟩ :=
    checkedEdges (exitCode := state.cfg.block .exit) checked
  rcases arms with ⟨yes, no⟩ | ⟨yes, no⟩
  · exact ⟨entry, ⟨.onTrue, yes⟩, ⟨.onFalse, no⟩, returns⟩
  · exact ⟨entry, ⟨.onFalse, no⟩, ⟨.onTrue, yes⟩, returns⟩

private theorem rewrite_target {Γ Δ : List Width} {index : Nat} {w : Width}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {rename : Rename Γ Δ} {keep : Var Δ w}
    {out : Block TargetOp (Label saved carried result (w :: extra)) Δ [result]}
    (emitted : rewriteAt? index rename keep code = some out) (slot : EdgeSlot) :
    (shape.ofBlock out).target slot = ((shape.ofBlock code).target slot).map liftTarget := by
  induction code generalizing index Δ with
  | terminator => simp [rewriteAt?] at emitted
  | @letOp _ _ width op operands rest ih =>
    cases index with
    | zero =>
      by_cases same : width = w
      · subst width
        simp only [rewriteAt?, dite_true, Option.some.injEq] at emitted
        rw [← emitted]
        exact AfterReorder.Second.Emit.liftCode_target rest (replaceBinding rename keep) keep slot
      · simp [rewriteAt?, same] at emitted
    | succ index =>
      simp only [rewriteAt?, Option.map_eq_some_iff] at emitted
      obtain ⟨next, rewritten, rfl⟩ := emitted
      exact ih (out := next) rewritten

private theorem emitAt_structure {args : List Width} {index : Nat} {w : Width}
    {op : TargetOp args w} {operands : Operands ((extra ++ [saved]) ++ Input) args}
    {source : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {target : Cfg TargetOp (Label saved carried result (w :: extra)) Input [result]}
    (emitted : emitAt? source index op operands = some target) :
    (∃ returns, target.block .exit = .terminator (.ret returns)) ∧
    ∀ slot, (shape target (some ⟨_, .header⟩)).target slot =
      ((shape source (some ⟨_, .header⟩)).target slot).map liftTarget := by
  obtain ⟨⟨_, _⟩, _, edited⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨_, rewrite, edited⟩ := Option.bind_eq_some_iff.mp edited
  cases exit : source.block .exit with
  | letOp => simp [exit] at edited
  | terminator term =>
    cases term with
    | br => simp [exit] at edited
    | condBr => simp [exit] at edited
    | ret returns =>
      simp only [exit] at edited
      cases edited
      exact ⟨⟨returns, rfl⟩, rewrite_target rewrite⟩

private theorem count_bindings {Γ : List Width}
    (code : Block TargetOp (Label saved carried result extra) Γ [result]) :
    (shape.ofBlock code).bindings = (Header.Earlier.operations code).length := by
  induction code with
  | terminator => rfl
  | letOp _ _ _ ih => simp only [shape.ofBlock, Header.Earlier.operations, List.length_cons, ih]

theorem emit_supported {request : Nomination} {moved : Layout.Move state}
    (supported : Discovery.supported? state = true) (accepted : Layout.emit? state request = some moved) :
    Discovery.supported? moved.next = true := by
  have ⟨append, _, _⟩ := Layout.emit?_spec accepted
  have ⟨_, indexed, _, _, emitted, erased, _⟩ := Step.emit_spec append
  obtain ⟨⟨_, returnEq⟩, headerSlots⟩ := emitAt_structure emitted
  rw [supported_eq, Bool.and_eq_true_iff]
  refine ⟨decide_eq_true ?_, ?_⟩
  · have inventory := of_decide_eq_true (Bool.and_eq_true_iff.mp ((supported_eq _).symm.trans supported)).1
    have operations := AfterReorder.Second.Emit.emitAt?_operations emitted
    have inRange := (List.getElem?_eq_some_iff.mp indexed).1
    have count := inventory.1
    change _ = (shape.ofBlock (state.reference.cfg.block .header)).bindings at count
    rw [count_bindings] at count
    have indexInHeader : moved.append.index < (Header.Earlier.operations (state.reference.cfg.block .header)).length :=
      count ▸ inRange
    change moved.append.next.origins.length =
      (shape.ofBlock (moved.append.next.cfg.block .header)).bindings ∧ moved.append.next.origins.Nodup
    refine ⟨?_, ?_⟩
    · rw [erased, count_bindings, operations, List.length_eraseIdx_of_lt inRange,
        List.length_eraseIdx_of_lt indexInHeader, count]
    · rw [erased]
      exact inventory.2.sublist (List.eraseIdx_sublist ..)
  · have checked := (Bool.and_eq_true_iff.mp ((supported_eq _).symm.trans supported)).2
    obtain ⟨entry, arms, _⟩ := checkedEdges (exitCode := state.cfg.block .exit) checked
    have entryLift (slot : EdgeSlot) :
        (shape moved.next.cfg none).target slot = ((shape state.cfg none).target slot).map liftTarget := by
      change (shape.ofBlock (moved.splice.leading.wrap
        (liftCode moved.splice.previous moved.splice.inserted state.tail))).target slot =
        ((shape.ofBlock (state.leading.wrap state.tail)).target slot).map liftTarget
      simp only [Saved.Prefix.wrap_targets, AfterReorder.Second.Emit.liftCode_target]
    change shapeCheck ((shape moved.next.cfg none).target .jump)
      ((shape moved.append.next.cfg savedHeader).target .onTrue)
      ((shape moved.append.next.cfg savedHeader).target .onFalse) (moved.append.next.cfg.block .exit) = true
    change ∀ slot, (shape moved.append.next.cfg savedHeader).target slot =
      ((shape state.cfg savedHeader).target slot).map liftTarget at headerSlots
    rw [entryLift, headerSlots .onTrue, headerSlots .onFalse, entry, returnEq]
    rcases arms with ⟨yes, no⟩ | ⟨yes, no⟩ <;> rw [yes, no] <;> rfl

private theorem header_path (supported : Discovery.supported? state = true) :
    EntryPath state.cfg savedHeader [savedHeader, none] :=
  (EntryPath.entry (cfg := state.cfg)).step .jump (edges supported).1

private theorem reachable (supported : Discovery.supported? state = true)
    (block : BlockId (Label saved carried result extra)) : Reachable state.cfg block := by
  rcases block with _ | ⟨_, label⟩
  · exact ⟨_, .entry⟩
  cases label
  · exact ⟨_, header_path supported⟩
  · obtain ⟨slot, edge⟩ := (edges supported).2.2.1
    exact ⟨_, (header_path supported).step slot edge⟩

private theorem backedge_endpoints (supported : Discovery.supported? state = true)
    {edge : Backedge (Label saved carried result extra)} (actual : LoopForest.ActualBackedge state.cfg edge) :
    some edge.header = savedHeader ∧ edge.latch = edge.header := by
  obtain ⟨target, latch, slot⟩ := edge
  rcases latch with ⟨_, latch⟩
  cases latch with
  | exit =>
    have impossible := (edges supported).2.2.2 slot
    have successor := actual.2.1
    rw [impossible] at successor
    contradiction
  | header =>
    rcases target with ⟨_, targetLabel⟩
    cases targetLabel with
    | header => exact ⟨rfl, rfl⟩
    | exit =>
      have visits := actual.2.2 _ (header_path supported)
      rcases List.mem_cons.mp visits with eq | listed
      · have distinguish := congrArg CrossBlock.blockNumber eq
        exact (by decide : (2 : Nat) ≠ 1) distinguish |>.elim
      · simp at listed

private theorem actual_exists (supported : Discovery.supported? state = true) :
    ∃ edge : Backedge (Label saved carried result extra),
      LoopForest.ActualBackedge state.cfg edge ∧ some edge.header = savedHeader := by
  obtain ⟨slot, edge⟩ := (edges supported).2.1
  refine ⟨⟨⟨_, .header⟩, ⟨_, .header⟩, slot⟩, ⟨⟨_, header_path supported⟩, edge, ?_⟩, rfl⟩
  intro past path
  cases path
  simp

private theorem checkClosed :
    let := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
    Dominance.checkClosed state.cfg intermediateBlocks = true := by
  let := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
  simp only [Dominance.checkClosed, List.all_eq_true, decide_eq_true_eq]
  exact fun _ _ edge _ => target_mem edge.2

private theorem checkInventory (supported : Discovery.supported? state = true)
    {tree : DominatorTree state.cfg} (complete : tree.Complete) :
    NaturalLoop.checkInventory tree intermediateBlocks = true := by
  simp only [NaturalLoop.checkInventory, List.all_eq_true, Bool.and_eq_true_iff]
  intro block _
  refine ⟨complete.reachable_complete (reachable supported block), fun slot _ => ?_⟩
  split
  · rfl
  · simpa only [decide_eq_true_eq] using vertices_mem _

private theorem loop_family (supported : Discovery.supported? state = true)
    {tree : DominatorTree state.cfg} (complete : tree.Complete)
    {loops : List (LoopForest.HeaderLoop (Label saved carried result extra))}
    (found : LoopForest.loops? tree intermediateBlocks = some loops) :
    ∃ loop, loops = [loop] ∧ ∀ block, block ∈ loop.members ↔ block = savedHeader := by
  obtain ⟨edge, actual, header⟩ := actual_exists supported
  have hasHeader := (LoopForest.mem_loopHeaders_iff found complete edge.header).mpr ⟨edge, actual, rfl⟩
  have subset : ∀ target ∈ loops.map LoopForest.HeaderLoop.header, target ∈ [edge.header] := by
    intro target listed
    obtain ⟨other, backedge, rfl⟩ := (LoopForest.mem_loopHeaders_iff found complete target).mp listed
    exact List.mem_singleton.mpr (Option.some.inj ((backedge_endpoints supported backedge).1.trans header.symm))
  have atMost := List.Nodup.length_le_of_subset (LoopForest.loopHeaders_nodup found) subset
  have nonempty : loops ≠ [] := by
    rintro rfl
    simp at hasHeader
  obtain ⟨loop, rfl⟩ : ∃ loop, loops = [loop] := by
    apply List.length_eq_one_iff.mp
    simp only [List.length_map, List.length_singleton] at atMost
    have := List.length_pos_iff.mpr nonempty
    omega
  have membership := LoopForest.mem_loop_iff found complete (loop := loop) (by simp)
  have headerEq : edge.header = loop.header := by simpa using hasHeader
  refine ⟨loop, rfl, fun block => ⟨?_, ?_⟩⟩
  · intro inside
    obtain ⟨actualEdge, backedge, _, eq | path⟩ := (membership block).mp inside
    · exact eq.trans (backedge_endpoints supported backedge).1
    · have same := (backedge_endpoints supported backedge).2
      have impossible : ∀ {b}, ¬ NaturalLoop.ToLatch state.cfg actualEdge b := by
        intro b path
        induction path with
        | latch _ avoids => exact avoids same
        | predecessor _ _ _ _ _ ih => exact ih
      exact (impossible path).elim
  · intro eq
    exact (membership block).mpr ⟨edge, actual, headerEq, .inl (eq.trans header.symm)⟩

theorem control_exists (supported : Discovery.supported? state = true) :
    ∃ control, CrossBlock.Control.check? state = some control := by
  let := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
  have success := (Dominance.Tree.Synthesis.synthesize?_isSome_iff (cfg := state.cfg)
    (blocks := intermediateBlocks) CrossBlock.blockNumber CrossBlock.blockNumber_injective).mpr checkClosed
  obtain ⟨tree, synthesized⟩ := Option.isSome_iff_exists.mp success
  have found : LoopForest.loops? tree.1 intermediateBlocks =
      some (LoopForest.coalesce tree.1 intermediateBlocks (LoopForest.scan tree.1 intermediateBlocks)) := by
    simp [LoopForest.loops?, LoopForest.discover?, checkInventory supported tree.2]
  obtain ⟨loop, singleton, _⟩ := loop_family supported tree.2 found
  rw [singleton] at found
  have forest := (LoopForest.forest_eq_some_iff [loop]).mpr ⟨found, by simp⟩
  unfold CrossBlock.Control.check?
  simp only [synthesized]
  dsimp only [Bind.bind, Option.bind]
  split
  next eq => rw [forest] at eq; contradiction
  next => exact ⟨_, rfl⟩

theorem control_depths (supported : Discovery.supported? state = true) (control : CrossBlock.Control state) :
    control.depth none = 0 ∧ control.depth savedHeader = 1 ∧ control.depth (some ⟨_, .exit⟩) = 0 := by
  obtain ⟨loop, singleton, membership⟩ :=
    loop_family supported control.complete ((LoopForest.forest_eq_some_iff _).mp control.checked).1
  have exitOutside : (some ⟨_, .exit⟩ : BlockId (Label saved carried result extra)) ≠ savedHeader := by
    intro eq
    have distinguish := congrArg CrossBlock.blockNumber eq
    exact (by decide : (2 : Nat) ≠ 1) distinguish |>.elim
  have entryOutside : (none : BlockId (Label saved carried result extra)) ≠ savedHeader := by
    intro eq
    contradiction
  simp [CrossBlock.Control.depth, LoopForest.depth, LoopForest.enclosing, singleton, membership,
    entryOutside, exitOutside]

theorem rank_exists {origin headerBudget : Nat} {kept : CrossBlock.Kept (Label saved carried result extra)}
    (supported : Discovery.supported? state = true) (live : CrossBlock.keep? state origin = some kept) :
    ∃ ranked, PreheaderSearch.rank? state origin headerBudget = some ranked := by
  obtain ⟨control, checked⟩ := control_exists supported
  obtain ⟨cursor, start⟩ : ∃ cursor, HeaderSplice.Walk.Cursor.check? state origin = some cursor := by
    unfold HeaderSplice.Walk.Cursor.check?
    split
    next eq => rw [live] at eq; contradiction
    next => exact ⟨_, rfl⟩
  unfold PreheaderSearch.rank? HeaderSplice.Walk.rank? CrossBlock.analyze? HeaderSplice.Walk.walk?
  simp only [PreheaderSearch.nomination, supported, ite_true, live, checked, start]
  exact ⟨_, rfl⟩

theorem ranked_selects_latest {origin headerBudget : Nat} {ranked : PreheaderSearch.Ranked state origin}
    (accepted : PreheaderSearch.rank? state origin headerBudget = some ranked) :
    ranked.crossBlock.selectedMove? = (PreheaderSearch.latest? state origin).map Prod.snd := by
  have analyzed := (HeaderSplice.Walk.rank?_spec accepted).1
  have supported := (CrossBlock.analyze?_spec analyzed).1
  obtain ⟨entryDepth, headerDepth, _⟩ := control_depths supported ranked.crossBlock.control
  simpa [CrossBlock.Analysis.selectedMove?, entryDepth, headerDepth] using PreheaderSearch.rank?_spec accepted

theorem hoist_none_iff {source : Layout.Output Input saved carried result} {origin : Nat}
    (supported : Discovery.supported? source.2 = true) :
    hoist? source origin = none ↔
      (CrossBlock.keep? source.2 origin = none ∨ PreheaderSearch.latest? source.2 origin = none) := by
  rw [PreheaderSearch.Sequence.Discovery.hoist?_none_iff]
  refine ⟨?_, ?_⟩
  · intro noHoist
    cases live : CrossBlock.keep? source.2 origin with
    | none => exact .inl rfl
    | some kept =>
      obtain ⟨ranked, accepted⟩ := rank_exists supported live (headerBudget := 0)
      have noneSelected := noHoist ranked accepted
      rw [ranked_selects_latest accepted, Option.map_eq_none_iff] at noneSelected
      exact .inr noneSelected
  · intro absent ranked accepted
    rcases absent with dead | noCut
    · have analyzed := (HeaderSplice.Walk.rank?_spec accepted).1
      have live := (CrossBlock.analyze?_spec analyzed).2.2.1
      change CrossBlock.keep? source.2 origin = some ranked.crossBlock.kept at live
      simp only [dead] at live
      contradiction
    · simp [ranked_selects_latest accepted, noCut]

theorem choose_none_iff {source : Layout.Output Input saved carried result}
    (supported : Discovery.supported? source.2 = true) :
    choose? source = none ↔ ∀ origin ∈ source.2.reference.origins,
      CrossBlock.keep? source.2 origin = none ∨
        ∀ cut ≤ source.2.savedCount, Layout.emit? source.2 ⟨origin, cut⟩ = none := by
  simp only [PreheaderSearch.Sequence.Discovery.choose?_none_iff, hoist_none_iff supported,
    PreheaderSearch.latest?_none]

private theorem collect_supported (source : Layout.Output Input saved carried result) (budget : Nat)
    (supported : Discovery.supported? source.2 = true) :
    Discovery.supported? (PreheaderSearch.Sequence.Discovery.collect source budget).output.2 = true := by
  induction budget generalizing source with
  | zero => exact supported
  | succ budget ih =>
    cases picked : choose? source with
    | none =>
      rw [PreheaderSearch.Sequence.Discovery.collect, picked]
      exact supported
    | some candidate =>
      rcases candidate with ⟨_, hoist⟩
      rw [PreheaderSearch.Sequence.Discovery.collect, picked]
      obtain ⟨_, emitted, _, output, _, _⟩ :=
        PreheaderSearch.Sequence.Discovery.hoist_moves hoist
      apply ih
      rw [output]
      exact emit_supported supported emitted

theorem schedule_terminal {source : Layout.Output Input saved carried result} {plan : Plan source}
    (accepted : schedule? source = some plan) :
    Discovery.supported? plan.output.2 = true ∧
    ∀ origin ∈ plan.output.2.reference.origins, CrossBlock.keep? plan.output.2 origin = none ∨
      ∀ cut ≤ plan.output.2.savedCount, Layout.emit? plan.output.2 ⟨origin, cut⟩ = none := by
  unfold schedule? at accepted
  split at accepted
  next supported =>
    cases accepted
    have outputSupported := collect_supported source source.2.reference.origins.length supported
    exact ⟨outputSupported, (choose_none_iff outputSupported).mp
      (PreheaderSearch.Sequence.Discovery.collect_terminal (Nat.le_refl _))⟩
  next => contradiction

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch
