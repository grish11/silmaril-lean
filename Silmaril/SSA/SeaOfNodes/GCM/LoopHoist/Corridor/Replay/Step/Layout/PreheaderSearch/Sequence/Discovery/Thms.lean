module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input : List Width} {saved carried result : Width} {origin : Nat}
variable {source : Layout.Output Input saved carried result} {plan : Plan source}

/-- A scan refusal rules out a preheader winner for every admitted rank of this origin. -/
theorem hoist?_none_iff :
    hoist? source origin = none ↔
    ∀ ranked, PreheaderSearch.rank? source.2 origin 0 = some ranked →
      ranked.crossBlock.selectedMove? = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.hoist?_none_iff

/-- The selected origin is in the current inventory and has the stated checked hoist. -/
theorem choose?_some {chosen : Hoist source origin} (found : choose? source = some ⟨origin, chosen⟩) :
    origin ∈ source.2.reference.origins ∧ hoist? source origin = some chosen :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.choose?_some found

/-- The scan fails exactly when each current identity has no admitted hoist. -/
theorem choose?_none_iff :
    choose? source = none ↔ ∀ origin ∈ source.2.reference.origins, hoist? source origin = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.choose?_none_iff

/-- The selected CFG is the real physical splice and removes exactly the resolved header position. -/
theorem hoist_moves (hoist : Hoist source origin) :
    ∃ cut, Layout.emit? source.2 ⟨origin, cut⟩ = some hoist.move ∧
      hoist.choice.ranked.selection.1 = ⟨none, cut⟩ ∧
      hoist.choice.ranked.selection.2 = ⟨_, hoist.move.next⟩ ∧
      source.2.reference.origins[hoist.move.append.index]? = some origin ∧
      hoist.choice.ranked.selection.2.2.reference.origins =
        source.2.reference.origins.eraseIdx hoist.move.append.index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.hoist_moves hoist

/-- Each admitted choice removes one surviving header origin. -/
theorem hoist_decreases (hoist : Hoist source origin) :
    hoist.choice.ranked.selection.2.2.reference.origins.length + 1 = source.2.reference.origins.length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.hoist_decreases hoist

/-- The discovered requests replay to the exact trace, including each intermediate layout. -/
theorem collect_replay (source : Layout.Output Input saved carried result) (budget position : Nat) :
    let plan := collect source budget
    Sequence.run source position plan.requests = .ok plan.trace :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.collect_replay source budget position

/-- The number of edits accounts for the decrease in the live inventory. -/
theorem collect_count (source : Layout.Output Input saved carried result) (budget : Nat) :
    let plan := collect source budget
    plan.output.2.reference.origins.length + plan.requests.length = source.2.reference.origins.length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.collect_count source budget

/-- A bound covering the inventory suffices to exhaust the current rank-selected hoists. -/
theorem collect_terminal {budget : Nat} (enough : source.2.reference.origins.length ≤ budget) :
    choose? (collect source budget).output = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.collect_terminal enough

/-- A successful schedule replays exactly and has no rank-selected hoist in its final live inventory. -/
theorem schedule?_spec (accepted : schedule? source = some plan) (position : Nat) :
    Layout.Discovery.supported? source.2 = true ∧
    Sequence.run source position plan.requests = .ok plan.trace ∧
    plan.output.2.reference.origins.length + plan.requests.length = source.2.reference.origins.length ∧
    ∀ origin ∈ plan.output.2.reference.origins, ∀ ranked,
      PreheaderSearch.rank? plan.output.2 origin 0 = some ranked →
        ranked.crossBlock.selectedMove? = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.schedule?_spec accepted position


variable {base : Silmaril.MLIR.CF.Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {inventory : List Nat} {input : Env Input} {values : Env (source.1 ++ [saved])}

/-- The scheduled trace transports the layout, saved inventory, packet and prefix invariants. -/
theorem plan_preserves (plan : Plan source) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    Layout.Invariant plan.output.2 ∧
    ∃ finalValues : Env (plan.output.1 ++ [saved]),
      Saved.Invariant base plan.output.2.cfg inventory plan.output.2.reference.origins
        plan.output.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches plan.output.2.reference.cfg.entry input finalValues :=
  Sequence.trace_preserves plan.trace valid prior matched

/-- Returns and exhaustion agree with the input at common block fuel. -/
theorem plan_run_eq (plan : Plan source) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = source.2.cfg.run evalOp fuel input :=
  Sequence.trace_run_eq plan.trace valid prior matched fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The exact scheduled output has the same partial denotation as the input. -/
theorem plan_denotePart (plan : Plan source) (valid : Layout.Invariant source.2)
    (prior : Saved.Invariant base source.2.cfg inventory source.2.reference.origins source.2.reference.slots input values)
    (matched : Saved.Prefix.Matches source.2.reference.cfg.entry input values) :
    (Cfg.embed plan.output.2.cfg).denotePart evalOp input = (Cfg.embed source.2.cfg).denotePart evalOp input :=
  Sequence.trace_denotePart plan.trace valid prior matched

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery
