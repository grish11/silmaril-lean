module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.Correctness

/-! # Admission and terminal hoist completeness for the saved single-latch CFG -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch

open Silmaril.MLIR.Arith (Width)
open AfterReorder.Second (savedHeader)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra}
variable {source : Layout.Output Input saved carried result}

/-- Every supported layout admits the existing synthesized control certificate. -/
theorem control_exists (supported : Layout.Discovery.supported? state = true) :
    ∃ control, CrossBlock.Control.check? state = some control :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.control_exists supported

/-- The checked forest counts the header self-loop once and excludes entry and exit. -/
theorem control_depths (supported : Layout.Discovery.supported? state = true) (control : CrossBlock.Control state) :
    control.depth none = 0 ∧ control.depth savedHeader = 1 ∧ control.depth (some ⟨_, .exit⟩) = 0 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.control_depths supported control

/-- A physical hoist retains the supported successor shape and updates the live inventory. -/
theorem emit_supported {request : Nomination} {moved : Layout.Move state}
    (supported : Layout.Discovery.supported? state = true) (accepted : Layout.emit? state request = some moved) :
    Layout.Discovery.supported? moved.next = true :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.emit_supported supported accepted

/-- On the supported shape a live, checked header origin always admits a rank. -/
theorem rank_exists {origin headerBudget : Nat} {kept : CrossBlock.Kept (Label saved carried result extra)}
    (supported : Layout.Discovery.supported? state = true) (live : CrossBlock.keep? state origin = some kept) :
    ∃ ranked, PreheaderSearch.rank? state origin headerBudget = some ranked :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.rank_exists supported live

/-- A rank selects its latest admitted preheader cut regardless of the header-walk budget. -/
theorem ranked_selects_latest {origin headerBudget : Nat} {ranked : PreheaderSearch.Ranked state origin}
    (accepted : PreheaderSearch.rank? state origin headerBudget = some ranked) :
    ranked.crossBlock.selectedMove? = (PreheaderSearch.latest? state origin).map Prod.snd :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.ranked_selects_latest accepted

/-- One origin is skipped exactly when the retained-header check fails or the physical search is empty. -/
theorem hoist_none_iff {origin : Nat} (supported : Layout.Discovery.supported? source.2 = true) :
    PreheaderSearch.Sequence.Discovery.hoist? source origin = none ↔
      (CrossBlock.keep? source.2 origin = none ∨ PreheaderSearch.latest? source.2 origin = none) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.hoist_none_iff supported

/-- A fixed point excludes a checked physical splice for every retained live origin and cut in the inventory. -/
theorem choose_none_iff (supported : Layout.Discovery.supported? source.2 = true) :
    PreheaderSearch.Sequence.Discovery.choose? source = none ↔ ∀ origin ∈ source.2.reference.origins,
      CrossBlock.keep? source.2 origin = none ∨
        ∀ cut ≤ source.2.savedCount, Layout.emit? source.2 ⟨origin, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.choose_none_iff supported

/-- Successful discovery ends on a supported layout with no checked live preheader splice left. -/
theorem schedule_terminal {plan : PreheaderSearch.Sequence.Discovery.Plan source}
    (accepted : PreheaderSearch.Sequence.Discovery.schedule? source = some plan) :
    Layout.Discovery.supported? plan.output.2 = true ∧
    ∀ origin ∈ plan.output.2.reference.origins, CrossBlock.keep? plan.output.2 origin = none ∨
      ∀ cut ≤ plan.output.2.savedCount, Layout.emit? plan.output.2 ⟨origin, cut⟩ = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch.schedule_terminal accepted

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.SingleLatch
