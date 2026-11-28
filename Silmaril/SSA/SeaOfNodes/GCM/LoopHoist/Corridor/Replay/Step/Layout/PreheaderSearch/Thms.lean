module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open AfterReorder.Second (savedHeader)
open Header.Typed (edgePackets)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra : List Width} {saved carried result : Width} {origin cut headerBudget : Nat}
variable {state : Layout.State Input saved carried result extra} {moved : Layout.Move state}
variable {ranked : Ranked state origin}

/-- The search returns a cut within the physical prefix and its exact checked emission. -/
theorem latest?_some (selected : latest? state origin = some (cut, moved)) :
    cut ≤ state.savedCount ∧ Layout.emit? state ⟨origin, cut⟩ = some moved :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.latest?_some selected

/-- Exhausting the search rules out every cut in the enumerated prefix. -/
theorem latest?_none :
    latest? state origin = none ↔ ∀ cut ≤ state.savedCount, Layout.emit? state ⟨origin, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.latest?_none

/-- The returned cut is latest among the enumerated accepted cuts for this origin. -/
theorem latest?_max (selected : latest? state origin = some (cut, moved))
    {other : Nat} {alternative : Layout.Move state} (inRange : other ≤ state.savedCount)
    (accepted : Layout.emit? state ⟨origin, other⟩ = some alternative) : other ≤ cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.latest?_max selected inRange accepted

/-- A position beyond the physical prefix is refused on an invariant layout. -/
theorem refuses_outOfRange (valid : Layout.Invariant state) (outside : state.savedCount < cut) :
    Layout.emit? state ⟨origin, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.refuses_outOfRange valid outside

/-- The emitter refuses a cut with an unavailable operand of this live binding. -/
theorem refuses_unavailable {kept : CrossBlock.Kept (Label saved carried result extra)}
    {operand : Point (Label saved carried result extra)}
    (supported : Layout.Discovery.supported? state = true)
    (ready : CrossBlock.keep? state origin = some kept)
    (read : operand ∈ kept.sites.operands) (missing : ¬ operand.AvailableAt state.cfg ⟨none, cut⟩) :
    Layout.emit? state ⟨origin, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.refuses_unavailable supported ready read missing

/-- A physical cut before an operand definition in the same preheader is refused. -/
theorem refuses_before_definition {kept : CrossBlock.Kept (Label saved carried result extra)}
    {operand : Point (Label saved carried result extra)}
    (supported : Layout.Discovery.supported? state = true)
    (ready : CrossBlock.keep? state origin = some kept)
    (read : operand ∈ kept.sites.operands) (entrySite : operand.block = none) (early : cut < operand.cut) :
    Layout.emit? state ⟨origin, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.refuses_before_definition supported ready read entrySite early

/-- A header operand cannot dominate the preheader, so every preheader cut is refused. -/
theorem refuses_header_operand {kept : CrossBlock.Kept (Label saved carried result extra)}
    {operand : Point (Label saved carried result extra)}
    (supported : Layout.Discovery.supported? state = true)
    (ready : CrossBlock.keep? state origin = some kept)
    (read : operand ∈ kept.sites.operands) (headerSite : operand.block = savedHeader) :
    Layout.emit? state ⟨origin, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.refuses_header_operand supported ready read headerSite

/-- The ranker offers exactly the checked splice from the physical search. -/
theorem rank?_spec (accepted : rank? state origin headerBudget = some ranked) :
    ranked.crossBlock.preheader = (latest? state origin).map Prod.snd :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.rank?_spec accepted

/-- The preheader alternative resolves the same binding, operand sites and exact use occurrences as the header walk. -/
theorem rank?_sites (accepted : rank? state origin headerBudget = some ranked)
    (found : latest? state origin = some (cut, moved)) :
    moved.append.index = ranked.walked.start.binding.index ∧
    ranked.walked.start.binding.sites =
      ⟨(state.atLayout moved.append.candidate).operands, moved.append.candidate.uses⟩ ∧
    Legal state.cfg ranked.walked.start.binding.sites.operands ranked.walked.start.binding.sites.uses ⟨none, cut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.rank?_sites accepted found

/-- Selecting the preheader returns the exact CFG emitted at the winning physical cut. -/
theorem rank?_hoist (accepted : rank? state origin headerBudget = some ranked)
    (chosen : ranked.crossBlock.selectedMove? = some moved) :
    ∃ cut, latest? state origin = some (cut, moved) ∧ ranked.selection.1 = ⟨none, cut⟩ ∧
      ranked.selection.2 = ⟨_, moved.next⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.rank?_hoist accepted chosen

/-- The selected block has minimum certified depth over the visited header and every admitted physical cut in the search. -/
theorem rank?_minDepth (accepted : rank? state origin headerBudget = some ranked) :
    ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth savedHeader ∧
    ∀ {other : Nat} {alternative : Layout.Move state}, other ≤ state.savedCount →
      Layout.emit? state ⟨origin, other⟩ = some alternative →
      ranked.crossBlock.control.depth ranked.selection.1.block ≤ ranked.crossBlock.control.depth none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.rank?_minDepth accepted

/-- Entry and feedback prepend the saved result. Both conditional occurrences retain their own argument packets. -/
theorem latest?_packets (selected : latest? state origin = some (cut, moved)) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    let value := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))
    Saved.StepRoutes state.cfg moved.next.cfg input values value ∧
    ∀ latch : BitVec carried.val,
      let source := (values.append (.cons latch .nil)).append input
      (moved.next.cfg.block .header).eval evalOp edgePackets (.cons value source) =
        ((state.cfg.block .header).eval evalOp edgePackets source).map
          (fun packet => (packet.1, Saved.prependFrame value packet.2)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.latest?_packets selected valid matched

/-- Both outcomes preserve finite returns and exhaustion at common block fuel. -/
theorem rank?_run_eq {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state origin headerBudget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) (fuel : Nat) :
    ranked.selection.2.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.rank?_run_eq accepted valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The selected CFG preserves partial denotation. -/
theorem rank?_denotePart {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
    (accepted : rank? state origin headerBudget = some ranked) (valid : Layout.Invariant state)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : RoutesWith base state.cfg input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    (Cfg.embed ranked.selection.2.2.cfg).denotePart evalOp input = (Cfg.embed state.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.rank?_denotePart accepted valid prior matched

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch
