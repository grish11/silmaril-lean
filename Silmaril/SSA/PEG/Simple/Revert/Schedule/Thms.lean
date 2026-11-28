module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.Schedule.Correctness

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule

open RVSDG (Tuple)
open While.Siblings (push)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results args outs : List (Ty Data)} {n l : Nat} {t : Ty Data}
variable {g : Graph P params results n l} {m : Interpretation.{u,v,w} P}

theorem Stage.read_pull (s : Stage g args outs) (values : g.Valuation m)
    (base : Index l) (r : Ref s.graph.sort t) (idx : Index s.loops) :
    Rules.readRef (s.pull m values base) r idx =
      Rules.readRef values (push s.addresses r) (embedIndex s.keys base idx) :=
  Proofs.read_pull s base r idx

/-- Local equations are the original equations with only the checked
boundary ports supplied as parameters. -/
theorem Stage.pull_solves (s : Stage g args outs) {env : Tuple m.Value params} {values : g.Valuation m}
    {bindings : Tuple (Ref g.sort) args} {input : Tuple m.Value args}
    (valid : s.Valid bindings) (solves : g.Solves m env values)
    (supplied : Realizes m values bindings input) (base : Index l) :
    s.graph.Solves m input (s.pull m values base) :=
  Proofs.pull_solves s valid solves supplied base

theorem Plan.exec_of_runFuel (p : Plan g args outs) (fuel : Nat) {input : Tuple m.Value args}
    {output : Tuple m.Value outs} (ran : p.runFuel m fuel input = some output) :
    Exec m p.revert input (some output) :=
  Proofs.Plan.run_sound p fuel ran

theorem Accepted.demandWellFounded (a : Accepted g) : WellFounded g.Demand :=
  g.demandWellFounded_of_check a.rank a.ranked

/-- A successful finite execution defines every scheduled first exit and
ordered boundary store, and returns the original graph's roots in order.
Each nested stage includes the child first exit at every continuing outer
activation. The direction from execution needs no slice totality. -/
theorem Accepted.observations_of_exec (a : Accepted g) (laws : a.plan.Laws m)
    (input : Tuple m.Value params) (base : Index l) {output : Tuple m.Value results}
    (ran : Exec m a.plan.revert input (some output)) :
    let values := g.denote m input a.demandWellFounded
    a.plan.Observations m values base g.roots output ∧
      g.observe m values base = output.map (fun _ => some) := by
  let solves := g.denote_solves m input a.demandWellFounded
  have seen := Proofs.observations_of_exec a.plan a.valid solves
    (Proofs.parameters_realized a.parameters solves) laws ran base
  exact ⟨seen, Proofs.observe_of_read base output (Proofs.observations_read a.plan base g.roots output seen)⟩

/-- Defined first exits and ordered boundary observations construct a
finite run if every region's required slices are defined. The converse
establishes each successful handoff before entering the next region. -/
theorem Accepted.exec_iff_observations (a : Accepted g) (laws : a.plan.Laws m)
    (input : Tuple m.Value params) (base : Index l) (output : Tuple m.Value results)
    (slices : a.plan.Slices m (g.denote m input a.demandWellFounded) base) :
    Exec m a.plan.revert input (some output) ↔
      a.plan.Observations m (g.denote m input a.demandWellFounded) base g.roots output :=
  ⟨fun ran => (a.observations_of_exec laws input base ran).1, fun observed => by
    let solves := g.denote_solves m input a.demandWellFounded
    exact Proofs.exec_of_observations a.plan a.valid solves (Proofs.parameters_realized a.parameters solves)
      laws base slices observed⟩

end Silmaril.SSA.PEG.Simple.Revert.Schedule
