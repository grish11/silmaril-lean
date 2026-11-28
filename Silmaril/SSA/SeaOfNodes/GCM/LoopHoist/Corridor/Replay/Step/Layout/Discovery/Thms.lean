module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
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
variable {plan : Plan Input saved carried result} {budget : Nat} {policy : Policy}

/-- On an invariant layout this list contains every physical cut accepted
    by the transition for the supplied original identity. -/
theorem mem_acceptedCuts_iff (valid : Layout.Invariant state) (origin cut : Nat) :
    cut ∈ acceptedCuts state origin ↔ ∃ moved, Layout.emit? state ⟨origin, cut⟩ = some moved :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.mem_acceptedCuts_iff valid origin cut

/-- The chosen cut is extremal among every certified candidate. Ties at
    that cut follow the current header order. -/
theorem chooseWith?_extremal (valid : Layout.Invariant state) (chosen : chooseWith? policy state = some (request, moved))
    {other : Nomination} {alternative : Layout.Move state} (accepted : Layout.emit? state other = some alternative) :
    policy.Preferred request.cut other.cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.chooseWith?_extremal valid chosen accepted

/-- No actual natural loop in a certified complete forest contains the
    anonymous entry, which is the only block where this emitter inserts. -/
theorem preheader_depth_eq_zero {tree : DominatorTree state.cfg}
    {loops : List (LoopForest.HeaderLoop (Label saved carried result extra))}
    (forest : LoopForest.forest? tree AfterReorder.Second.intermediateBlocks = some loops)
    (complete : tree.Complete) : LoopForest.depth tree loops none = 0 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.preheader_depth_eq_zero forest complete

/-- Every supported candidate is at depth zero in the actual forest.
    The latest policy maximizes the physical cut among those candidates. -/
theorem chooseLatest_minimal (valid : Layout.Invariant state) (chosen : chooseWith? .latest state = some (request, moved))
    {tree : DominatorTree state.cfg} {loops : List (LoopForest.HeaderLoop (Label saved carried result extra))}
    (forest : LoopForest.forest? tree AfterReorder.Second.intermediateBlocks = some loops) (complete : tree.Complete)
    {other : Nomination} {alternative : Layout.Move state} (accepted : Layout.emit? state other = some alternative) :
    LoopForest.depth tree loops none = 0 ∧ other.cut ≤ request.cut :=
  ⟨preheader_depth_eq_zero forest complete, chooseWith?_extremal valid chosen accepted⟩

/-- A selected request is accepted by the actual layout transition. -/
theorem chooseWith?_spec (chosen : chooseWith? policy state = some (request, moved)) :
    request.origin ∈ state.reference.origins ∧ request.cut ≤ state.savedCount ∧
      Layout.emit? state request = some moved :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.chooseWith?_spec chosen

theorem chooseWith?_legal (chosen : chooseWith? policy state = some (request, moved)) :
    Legal state.cfg (state.atLayout moved.append.candidate).operands moved.append.candidate.uses ⟨none, request.cut⟩ :=
  (Layout.emit?_placement (chooseWith?_spec chosen).2.2).2.2.1

/-- On a checked layout the enumerated cuts cover every accepted placement. -/
theorem chooseWith?_none_iff (valid : Layout.Invariant state) :
    chooseWith? policy state = none ↔ ∀ request, Layout.emit? state request = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.chooseWith?_none_iff valid

/-- Checked replay of the discovered requests returns the exact emitted state. -/
theorem collectWith_replay (policy : Policy) (budget position : Nat) :
    Layout.run state position (collectWith policy state budget).requests = .ok (collectWith policy state budget).output :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.collectWith_replay policy budget position

/-- The list respects the bound and the stop reason describes its terminal CFG. -/
theorem collectWith_stops (policy : Policy) (valid : Layout.Invariant state) (budget : Nat) :
    (collectWith policy state budget).requests.length ≤ budget ∧ (collectWith policy state budget).stopSpec budget :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.collectWith_stops policy valid budget

/-- A budget covering the live origins suffices to exhaust the supported profile. -/
theorem collectWith_fixedPoint {budget : Nat} (enough : state.reference.origins.length ≤ budget) :
    (collectWith policy state budget).stop = .fixedPoint :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.collectWith_fixedPoint enough

/-- Successful discovery starts from a checked prefix and shape. The returned
    plan replays exactly, preserves the layout invariant and respects its bound. -/
theorem discoverWith_spec (accepted : discoverWith policy reference budget = .ok plan) (position : Nat) :
    ∃ state, Layout.initial? reference = some state ∧ supported? state = true ∧
      Layout.run state position plan.requests = .ok plan.output ∧ Layout.Invariant plan.output.2 ∧
      plan.requests.length ≤ budget ∧ plan.stopSpec budget :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_spec accepted position

/-- On a supported seed the live header size suffices as the move budget. -/
theorem discoverWith_fixedPoint (accepted : discoverWith policy reference budget = .ok plan)
    (enough : reference.origins.length ≤ budget) : plan.stop = .fixedPoint :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_fixedPoint accepted enough

/-- The logical reference is the exact checked append replay of the same identities. -/
theorem discoverWith_append_replay (accepted : discoverWith policy reference budget = .ok plan) (position : Nat) :
    Step.run reference position (Layout.appendPlan (extra ++ [saved]).length plan.requests) =
      .ok ⟨plan.output.1, plan.output.2.reference⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_append_replay accepted position

/-- The actual emitted CFG retains the exact packet invariant of the certified base. -/
theorem discoverWith_packets (accepted : discoverWith policy reference budget = .ok plan)
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : Saved.Invariant base reference.cfg inventory reference.origins reference.slots input values)
    (matched : Saved.Prefix.Matches reference.cfg.entry input values) :
    ∃ finalValues : Env (plan.output.1 ++ [saved]),
      Saved.Invariant base plan.output.2.cfg inventory plan.output.2.reference.origins
        plan.output.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches plan.output.2.reference.cfg.entry input finalValues :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_packets accepted prior matched

/-- The emitted and reference CFGs agree at every common block fuel. -/
theorem discoverWith_run_eq (accepted : discoverWith policy reference budget = .ok plan) (input : Env Input) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = plan.output.2.reference.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_run_eq accepted input fuel

/-- Changing only the physical cuts leaves the exact checked append reference. -/
theorem discoverWith_reference_eq {otherPolicy : Policy} {otherBudget : Nat}
    {otherPlan : Plan Input saved carried result}
    (left : discoverWith policy reference budget = .ok plan)
    (right : discoverWith otherPolicy reference otherBudget = .ok otherPlan)
    (same : plan.requests.map Nomination.origin = otherPlan.requests.map Nomination.origin) :
    (⟨plan.output.1, plan.output.2.reference⟩ : Step.Output Input saved carried result) =
      ⟨otherPlan.output.1, otherPlan.output.2.reference⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_reference_eq left right same

/-- Two policies choosing the same origin order preserve every finite result on the same block fuel. -/
theorem discoverWith_sameOrigins_run_eq {otherPolicy : Policy} {otherBudget : Nat}
    {otherPlan : Plan Input saved carried result}
    (left : discoverWith policy reference budget = .ok plan)
    (right : discoverWith otherPolicy reference otherBudget = .ok otherPlan)
    (same : plan.requests.map Nomination.origin = otherPlan.requests.map Nomination.origin)
    (input : Env Input) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = otherPlan.output.2.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_sameOrigins_run_eq left right same input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The emitted and reference CFGs have the same partial denotation. -/
theorem discoverWith_denotePart (accepted : discoverWith policy reference budget = .ok plan) (input : Env Input) :
    (Cfg.embed plan.output.2.cfg).denotePart evalOp input =
      (Cfg.embed plan.output.2.reference.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_denotePart accepted input

/-- From the verified native seed, CFG fuel is the backedge budget plus three. -/
theorem discoverWith_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {plan : Plan Input two.prepared.intermediate.1 carried result}
    (seed : Replay.replay g header [producer, consumer] = .ok (.two record consumer two))
    (accepted : discoverWith policy (Step.fromTwo record consumer two) budget = .ok plan)
    (input : Env Input) (backedges : Nat) :
    plan.output.2.cfg.run evalOp (backedges + 3) input =
      (g.evalBackedges model backedges (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.discoverWith_fromTwo_budget seed accepted input backedges


/-! The earliest-first interface from the original discovery driver. -/

theorem choose?_spec (chosen : choose? state = some (request, moved)) :
    request.origin ∈ state.reference.origins ∧ request.cut ≤ state.savedCount ∧
      Layout.emit? state request = some moved :=
  chooseWith?_spec (policy := .earliest) chosen

theorem choose?_legal (chosen : choose? state = some (request, moved)) :
    Legal state.cfg (state.atLayout moved.append.candidate).operands moved.append.candidate.uses ⟨none, request.cut⟩ :=
  (Layout.emit?_placement (choose?_spec chosen).2.2).2.2.1

theorem choose?_none_iff (valid : Layout.Invariant state) :
    choose? state = none ↔ ∀ request, Layout.emit? state request = none :=
  chooseWith?_none_iff (policy := .earliest) valid

theorem collect_replay (budget position : Nat) :
    Layout.run state position (collect state budget).requests = .ok (collect state budget).output :=
  collectWith_replay .earliest budget position

theorem collect_stops (valid : Layout.Invariant state) (budget : Nat) :
    (collect state budget).requests.length ≤ budget ∧ (collect state budget).stopSpec budget :=
  collectWith_stops .earliest valid budget

theorem collect_fixedPoint {budget : Nat} (enough : state.reference.origins.length ≤ budget) :
    (collect state budget).stop = .fixedPoint :=
  collectWith_fixedPoint (policy := .earliest) enough

theorem discover_spec (accepted : discover reference budget = .ok plan) (position : Nat) :
    ∃ state, Layout.initial? reference = some state ∧ supported? state = true ∧
      Layout.run state position plan.requests = .ok plan.output ∧ Layout.Invariant plan.output.2 ∧
      plan.requests.length ≤ budget ∧ plan.stopSpec budget :=
  discoverWith_spec (policy := .earliest) accepted position

theorem discover_fixedPoint (accepted : discover reference budget = .ok plan)
    (enough : reference.origins.length ≤ budget) : plan.stop = .fixedPoint :=
  discoverWith_fixedPoint (policy := .earliest) accepted enough

theorem discover_append_replay (accepted : discover reference budget = .ok plan) (position : Nat) :
    Step.run reference position (Layout.appendPlan (extra ++ [saved]).length plan.requests) =
      .ok ⟨plan.output.1, plan.output.2.reference⟩ :=
  discoverWith_append_replay (policy := .earliest) accepted position

theorem discover_packets (accepted : discover reference budget = .ok plan)
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : Saved.Invariant base reference.cfg inventory reference.origins reference.slots input values)
    (matched : Saved.Prefix.Matches reference.cfg.entry input values) :
    ∃ finalValues : Env (plan.output.1 ++ [saved]),
      Saved.Invariant base plan.output.2.cfg inventory plan.output.2.reference.origins
        plan.output.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches plan.output.2.reference.cfg.entry input finalValues :=
  discoverWith_packets (policy := .earliest) accepted prior matched

theorem discover_run_eq (accepted : discover reference budget = .ok plan) (input : Env Input) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = plan.output.2.reference.cfg.run evalOp fuel input :=
  discoverWith_run_eq (policy := .earliest) accepted input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem discover_denotePart (accepted : discover reference budget = .ok plan) (input : Env Input) :
    (Cfg.embed plan.output.2.cfg).denotePart evalOp input =
      (Cfg.embed plan.output.2.reference.cfg).denotePart evalOp input :=
  discoverWith_denotePart (policy := .earliest) accepted input

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
  discoverWith_fromTwo_budget (policy := .earliest) seed accepted input backedges

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery
