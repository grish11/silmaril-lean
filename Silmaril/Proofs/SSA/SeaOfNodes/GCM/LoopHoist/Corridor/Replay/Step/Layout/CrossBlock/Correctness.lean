module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.MLIR.SCF (For)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock
open AfterReorder.Second (Candidate findCaptured? intermediateBlocks savedHeader targetDecEqWith)
open Loop.MLIR.CF (Program TargetOp evalOp model)

variable {Input extra Γ : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra} {request : Nomination} {analysis : Analysis state}

private theorem operandSites_captured {args : List Width} {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {operands : Operands Γ args} {captured : Operands ((extra ++ [saved]) ++ Input) args}
    (found : captureOrigins? origins operands = some captured) :
    operandSites state origins operands =
      Layout.physicalSites state.savedCount (For.renameOperands state.toPhysical captured) := by
  induction operands with
  | nil =>
    cases found
    rfl
  | cons ref tail ih =>
    cases origin : origins ref with
    | inr cut => simp [captureOrigins?, origin] at found
    | inl head =>
      simp only [captureOrigins?, origin, Option.map_eq_some_iff] at found
      obtain ⟨rest, matched, rfl⟩ := found
      simp only [Layout.CrossBlock.operandSites, origin, For.renameOperands, Layout.physicalSites, ih matched]

theorem findSites?_capture {index cursor : Nat} {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra}
    (found : findCaptured? index cursor origins code = some candidate) :
    findSites? state index cursor origins code =
      some ⟨(state.atLayout candidate).operands, candidate.uses⟩ := by
  induction code generalizing index cursor with
  | terminator => simp [findCaptured?] at found
  | letOp op operands tail ih =>
    cases index with
    | zero =>
      cases captured : captureOrigins? origins operands with
      | none => simp [findCaptured?, captured] at found
      | some inputs =>
        simp [findCaptured?, captured] at found
        subst candidate
        simp only [findSites?, operandSites_captured (state := state) captured,
          Layout.State.atLayout, Layout.State.physicalOperands]
    | succ index => exact ih found

theorem keep?_spec {origin : Nat} {kept : Kept (Label saved carried result extra)}
    (accepted : keep? state origin = some kept) :
    state.reference.origins.idxOf? origin = some kept.index ∧
    findSites? state kept.index 0 (Saved.origins (extra ++ [saved])) (state.cfg.block .header) = some kept.sites ∧
    kept.sites.uses ≠ [] ∧ Legal state.cfg kept.sites.operands kept.sites.uses kept.point := by
  obtain ⟨index, located, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨sites, found, decided⟩ := Option.bind_eq_some_iff.mp rest
  dsimp only at decided
  split at decided
  next checked =>
    cases decided
    let _ := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
    obtain ⟨live, legal⟩ := Bool.and_eq_true_iff.mp checked
    refine ⟨located, found, ?_, (Dominance.Placement.checkCut_iff.mp legal).2⟩
    simpa using live
  next => cases decided

theorem analyze?_spec (accepted : analyze? state request = some analysis) :
    Layout.Discovery.supported? state = true ∧ analysis.request = request ∧
      keep? state request.origin = some analysis.kept ∧
      Control.check? state = some analysis.control ∧ analysis.preheader = Layout.emit? state request := by
  simp only [analyze?] at accepted
  split at accepted
  next supported =>
    obtain ⟨kept, found, rest⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨control, computed, out⟩ := Option.bind_eq_some_iff.mp rest
    cases out
    exact ⟨supported, rfl, found, computed, rfl⟩
  next => cases accepted

private theorem supported_nodup (supported : Layout.Discovery.supported? state = true) :
    state.reference.origins.Nodup := (of_decide_eq_true (Bool.and_eq_true_iff.mp supported).1).2

theorem emit?_sites {kept : Kept (Label saved carried result extra)} {moved : Layout.Move state}
    (supported : Layout.Discovery.supported? state = true) (ready : keep? state request.origin = some kept)
    (emitted : Layout.emit? state request = some moved) :
    moved.append.index = kept.index ∧
    kept.sites = ⟨(state.atLayout moved.append.candidate).operands, moved.append.candidate.uses⟩ ∧
    Legal state.cfg kept.sites.operands kept.sites.uses ⟨none, request.cut⟩ := by
  obtain ⟨located, scan, _, _⟩ := keep?_spec ready
  obtain ⟨atIndex, found, available, _⟩ := Layout.emit?_placement emitted
  obtain ⟨bound, value, _⟩ := List.idxOf?_eq_some_iff.mp located
  have sameOrigin := (List.getElem?_eq_some_iff.mpr ⟨bound, value⟩).trans atIndex.symm
  have sameIndex := ((supported_nodup supported).eq_of_getElem?_eq bound sameOrigin).symm
  have sameSites := findSites?_capture (state := state) found
  rw [sameIndex, scan] at sameSites
  have equal := Option.some.inj sameSites
  exact ⟨sameIndex, equal, by rw [equal]; exact available⟩

theorem analyze?_candidates (accepted : analyze? state request = some analysis) :
    Legal state.cfg analysis.kept.sites.operands analysis.kept.sites.uses analysis.kept.point ∧
    ∀ moved, analysis.preheader = some moved →
      moved.append.index = analysis.kept.index ∧
      analysis.kept.sites = ⟨(state.atLayout moved.append.candidate).operands, moved.append.candidate.uses⟩ ∧
      Legal state.cfg analysis.kept.sites.operands analysis.kept.sites.uses ⟨none, request.cut⟩ := by
  obtain ⟨supported, _, kept, _, proposed⟩ := analyze?_spec accepted
  exact ⟨(keep?_spec kept).2.2.2, fun _ tried => emit?_sites supported kept (proposed.symm.trans tried)⟩

theorem analyze?_refuses_local (accepted : analyze? state request = some analysis)
    {operand : Point (Label saved carried result extra)} (read : operand ∈ analysis.kept.sites.operands)
    (localSite : operand.block = savedHeader) :
    analysis.preheader = none := by
  cases tried : analysis.preheader with
  | none => rfl
  | some moved =>
    have legal := ((analyze?_candidates accepted).2 moved tried).2.2
    have dominated := (legal.operands_available operand read).2.dominates
    rw [localSite] at dominated
    have impossible := dominated [none] EntryPath.entry
    simp [savedHeader] at impossible

theorem header_later (control : Control state) :
    (control.tree.address none).length < (control.tree.address savedHeader).length := by
  rw [control.tree.entry_address]
  apply List.length_pos_iff.mpr
  intro empty
  have same := control.tree.address_injective (empty.trans control.tree.entry_address.symm)
  cases same

theorem selected_minDepth (analysis : Analysis state) :
    analysis.control.depth analysis.point.block ≤ analysis.control.depth savedHeader ∧
    (analysis.preheader.isSome → analysis.control.depth analysis.point.block ≤ analysis.control.depth none) ∧
    (analysis.control.depth none = analysis.control.depth savedHeader → analysis.point = analysis.kept.point) := by
  by_cases less : analysis.control.depth none < analysis.control.depth savedHeader
  · cases proposed : analysis.preheader with
    | none => simp [Analysis.point, Analysis.selectedMove?, Kept.point, less, proposed]
    | some moved => simp [Analysis.point, Analysis.selectedMove?, less, proposed, Nat.le_of_lt less, Nat.ne_of_lt less]
  · simp [Analysis.point, Analysis.selectedMove?, Kept.point, less, Nat.le_of_not_gt less]

private theorem selected_emits {moved : Layout.Move state}
    (accepted : analyze? state request = some analysis) (selected : analysis.selectedMove? = some moved) :
    Layout.emit? state analysis.request = some moved := by
  obtain ⟨_, nominated, _, _, compiled⟩ := analyze?_spec accepted
  unfold Analysis.selectedMove? at selected
  split at selected
  · rw [nominated, ← compiled]
    exact selected
  · cases selected

theorem analyze?_replay (accepted : analyze? state request = some analysis) (position : Nat) :
    Layout.run state position analysis.requests = .ok analysis.output := by
  cases selected : analysis.selectedMove? with
  | none => simp [Analysis.requests, Analysis.output, selected, Layout.run]
  | some moved => simp [Analysis.requests, Analysis.output, selected, Layout.run, selected_emits accepted selected]

theorem analyze?_preheader_routes {moved : Layout.Move state}
    (accepted : analyze? state request = some analysis) (emitted : analysis.preheader = some moved)
    (valid : Layout.Invariant state) {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    Saved.StepRoutes state.cfg moved.next.cfg input values
      (evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))) :=
  Layout.emit?_routes valid ((analyze?_spec accepted).2.2.2.2.symm.trans emitted) matched

theorem analyze?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : analyze? state request = some analysis) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    analysis.output.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input := by
  cases selected : analysis.selectedMove? with
  | none => rw [Analysis.output, selected]
  | some moved =>
    rw [Analysis.output, selected]
    exact Saved.extend_run_eq prior (Layout.emit?_routes valid (selected_emits accepted selected) matched) fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem analyze?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : analyze? state request = some analysis) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed analysis.output.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input := by
  apply Part.ext
  intro value
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, analyze?_run_eq accepted valid prior matched]

theorem analyze?_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {state : Layout.State Input two.prepared.intermediate.1 carried result [two.prepared.consumer.width]}
    {analysis : Analysis state}
    (seed : replay g header [producer, consumer] = .ok (.two record consumer two))
    (initialized : Layout.initial? (Step.fromTwo record consumer two) = some state)
    (accepted : analyze? state request = some analysis) (input : Env Input) (budget : Nat) :
    analysis.output.2.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Layout.run_fromTwo_budget seed initialized (analyze?_replay accepted 2) input budget

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock
