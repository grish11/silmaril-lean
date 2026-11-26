module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (Program TargetOp evalOp model)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra} {request : Nomination} {moved : Layout.Move state}
variable {reference : Step.State Input saved carried result extra}
variable {plan : Plan Input saved carried result} {budget : Nat}

/-- A selected request is accepted by the actual layout transition. -/
theorem choose?_spec (chosen : choose? state = some (request, moved)) :
    request.origin ∈ state.reference.origins ∧ request.cut ≤ state.savedCount ∧
      Layout.emit? state request = some moved :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.choose?_spec chosen

theorem choose?_legal (chosen : choose? state = some (request, moved)) :
    Legal state.cfg (state.atLayout moved.append.candidate).operands moved.append.candidate.uses ⟨none, request.cut⟩ :=
  (Layout.emit?_placement (choose?_spec chosen).2.2).2.2.1

/-- On a checked layout the enumerated cuts cover every accepted placement. -/
theorem choose?_none_iff (valid : Layout.Invariant state) :
    choose? state = none ↔ ∀ request, Layout.emit? state request = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.choose?_none_iff valid

/-- Checked replay of the discovered requests returns the exact emitted state. -/
theorem collect_replay (budget position : Nat) :
    Layout.run state position (collect state budget).requests = .ok (collect state budget).output :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.collect_replay budget position

/-- The list respects the bound and the stop reason describes its terminal CFG. -/
theorem collect_stops (valid : Layout.Invariant state) (budget : Nat) :
    (collect state budget).requests.length ≤ budget ∧ (collect state budget).stopSpec budget :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.collect_stops valid budget

/-- A budget covering the live origins suffices to exhaust the supported profile. -/
theorem collect_fixedPoint {budget : Nat} (enough : state.reference.origins.length ≤ budget) :
    (collect state budget).stop = .fixedPoint :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.collect_fixedPoint enough

/-- Successful discovery starts from a checked prefix and shape. The returned
    plan replays exactly, preserves the layout invariant and respects its bound. -/
theorem discover_spec (accepted : discover reference budget = .ok plan) (position : Nat) :
    ∃ state, Layout.initial? reference = some state ∧ supported? state = true ∧
      Layout.run state position plan.requests = .ok plan.output ∧ Layout.Invariant plan.output.2 ∧
      plan.requests.length ≤ budget ∧ plan.stopSpec budget :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discover_spec accepted position

/-- On a supported seed the live header size suffices as the move budget. -/
theorem discover_fixedPoint (accepted : discover reference budget = .ok plan)
    (enough : reference.origins.length ≤ budget) : plan.stop = .fixedPoint :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discover_fixedPoint accepted enough

/-- The logical reference is the exact checked append replay of the same identities. -/
theorem discover_append_replay (accepted : discover reference budget = .ok plan) (position : Nat) :
    Step.run reference position (Layout.appendPlan (extra ++ [saved]).length plan.requests) =
      .ok ⟨plan.output.1, plan.output.2.reference⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discover_append_replay accepted position

/-- The actual emitted CFG retains the exact packet invariant of the certified base. -/
theorem discover_packets (accepted : discover reference budget = .ok plan)
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : Saved.Invariant base reference.cfg inventory reference.origins reference.slots input values)
    (matched : Saved.Prefix.Matches reference.cfg.entry input values) :
    ∃ finalValues : Env (plan.output.1 ++ [saved]),
      Saved.Invariant base plan.output.2.cfg inventory plan.output.2.reference.origins
        plan.output.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches plan.output.2.reference.cfg.entry input finalValues :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discover_packets accepted prior matched

/-- The emitted and reference CFGs agree at every common block fuel. -/
theorem discover_run_eq (accepted : discover reference budget = .ok plan) (input : Env Input) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = plan.output.2.reference.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discover_run_eq accepted input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The emitted and reference CFGs have the same partial denotation. -/
theorem discover_denotePart (accepted : discover reference budget = .ok plan) (input : Env Input) :
    (Cfg.embed plan.output.2.cfg).denotePart evalOp input =
      (Cfg.embed plan.output.2.reference.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discover_denotePart accepted input

/-- From the verified native seed, CFG fuel is the backedge budget plus three. -/
theorem discover_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {plan : Plan Input two.prepared.intermediate.1 carried result}
    (seed : Replay.replay g header [producer, consumer] = .ok (.two record consumer two))
    (accepted : discover (Step.fromTwo record consumer two) budget = .ok plan)
    (input : Env Input) (backedges : Nat) :
    plan.output.2.cfg.run evalOp (backedges + 3) input =
      (g.evalBackedges model backedges (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discover_fromTwo_budget seed accepted input backedges

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery
