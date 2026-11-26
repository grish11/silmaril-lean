module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg)
open AfterReorder.Second (Candidate findCaptured? savedHeader)
open Loop.MLIR.CF (Program TargetOp evalOp model)

variable {Input extra Γ : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra} {request : Nomination} {analysis : Analysis state}

theorem Control.entry_depth_eq_zero (control : Control state) : control.depth none = 0 :=
  Layout.Discovery.preheader_depth_eq_zero control.checked control.complete

/-- A captured binding and the retained-header scan agree on physical definition sites
    and every ordinary and exact incoming Φ use. -/
theorem findSites?_capture {index cursor : Nat} {origins : Origins ((extra ++ [saved]) ++ Input) Γ}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {candidate : Candidate Input saved carried result extra}
    (found : findCaptured? index cursor origins code = some candidate) :
    findSites? state index cursor origins code =
      some ⟨(state.atLayout candidate).operands, candidate.uses⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.findSites?_capture found

/-- The original binding has a live use and its unchanged cut passes the current CFG check. -/
theorem keep?_spec {origin : Nat} {kept : Kept (Label saved carried result extra)}
    (accepted : keep? state origin = some kept) :
    state.reference.origins.idxOf? origin = some kept.index ∧
    findSites? state kept.index 0 (Saved.origins (extra ++ [saved])) (state.cfg.block .header) = some kept.sites ∧
    kept.sites.uses ≠ [] ∧ Legal state.cfg kept.sites.operands kept.sites.uses kept.point :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.keep?_spec accepted

/-- The analysis uses the checked actual forest and the exact preheader splice attempt. -/
theorem analyze?_spec (accepted : analyze? state request = some analysis) :
    Layout.Discovery.supported? state = true ∧ analysis.request = request ∧
      keep? state request.origin = some analysis.kept ∧
      Control.check? state = some analysis.control ∧ analysis.preheader = Layout.emit? state request :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_spec accepted

/-- A checked physical splice resolves the same live binding and sites as
    the retained header candidate. -/
theorem emit?_sites {kept : Kept (Label saved carried result extra)} {moved : Layout.Move state}
    (supported : Layout.Discovery.supported? state = true) (ready : keep? state request.origin = some kept)
    (emitted : Layout.emit? state request = some moved) :
    moved.append.index = kept.index ∧
    kept.sites = ⟨(state.atLayout moved.append.candidate).operands, moved.append.candidate.uses⟩ ∧
    Legal state.cfg kept.sites.operands kept.sites.uses ⟨none, request.cut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.emit?_sites supported ready emitted

/-- Both admitted candidates are legal for the same current binding and the same use occurrences. -/
theorem analyze?_candidates (accepted : analyze? state request = some analysis) :
    Legal state.cfg analysis.kept.sites.operands analysis.kept.sites.uses analysis.kept.point ∧
    ∀ moved, analysis.preheader = some moved →
      moved.append.index = analysis.kept.index ∧
      analysis.kept.sites = ⟨(state.atLayout moved.append.candidate).operands, moved.append.candidate.uses⟩ ∧
      Legal state.cfg analysis.kept.sites.operands analysis.kept.sites.uses ⟨none, request.cut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_candidates accepted

/-- A header-local operand cannot be read at the preheader. The header remains an alternative. -/
theorem analyze?_refuses_local (accepted : analyze? state request = some analysis)
    {operand : Point (Label saved carried result extra)} (read : operand ∈ analysis.kept.sites.operands)
    (localSite : operand.block = savedHeader) :
    analysis.preheader = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_refuses_local accepted read localSite

/-- The header is the later control position by the certified dominator address length. -/
theorem header_later (control : Control state) :
    (control.tree.address none).length < (control.tree.address savedHeader).length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.header_later control

/-- Choose minimum actual loop depth among the admitted pair. Equal depths retain the header. -/
theorem selected_minDepth (analysis : Analysis state) :
    analysis.control.depth analysis.point.block ≤ analysis.control.depth savedHeader ∧
    (analysis.preheader.isSome → analysis.control.depth analysis.point.block ≤ analysis.control.depth none) ∧
    (analysis.control.depth none = analysis.control.depth savedHeader → analysis.point = analysis.kept.point) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.selected_minDepth analysis

/-- Selection returns the exact checked replay result, including the zero-move case. -/
theorem analyze?_replay (accepted : analyze? state request = some analysis) (position : Nat) :
    Layout.run state position analysis.requests = .ok analysis.output :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_replay accepted position

/-- An admitted preheader splice carries the saved word on entry and feedback and retains the exact exit. -/
theorem analyze?_preheader_routes {moved : Layout.Move state}
    (accepted : analyze? state request = some analysis) (emitted : analysis.preheader = some moved)
    (valid : Layout.Invariant state) {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    Saved.StepRoutes state.cfg moved.next.cfg input values
      (evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_preheader_routes accepted emitted valid matched

/-- The selected CFG agrees at every common block fuel under the existing packet invariant. -/
theorem analyze?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : analyze? state request = some analysis) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    analysis.output.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_run_eq accepted valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The selected CFG has the same partial denotation as the existing layout. -/
theorem analyze?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : analyze? state request = some analysis) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed analysis.output.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_denotePart accepted valid prior matched

/-- Both supported placements have the same native backedge-to-block fuel offset. -/
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
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.analyze?_fromTwo_budget seed initialized accepted input budget

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock
