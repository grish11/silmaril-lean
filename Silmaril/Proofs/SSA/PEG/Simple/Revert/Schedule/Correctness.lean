module

public import Silmaril.Proofs.SSA.PEG.Simple.Revert.Schedule.Transport
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Thms
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Proofs

open RVSDG (Port Tuple)
open While.Siblings (push)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results args mid outs : List (Ty Data)} {n l rows loops : Nat} {t : Ty Data}
variable {g : Graph P params results n l} {localGraph : Graph P args outs rows loops}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params} {values : g.Valuation m}

private theorem seq_some {a : Stmt P true args mid} {b : Stmt P true mid outs}
    {input : Tuple m.Value args} {result : Tuple m.Value outs}
    (ran : Exec m (.seq a b) input (some result)) :
    ∃ next, Exec m a input (some next) ∧ Exec m b next (some result) := by
  cases ran with | seq first second => exact ⟨_, first, second⟩

private theorem project_eq {slots : Tuple (Port args) outs}
    {input : Tuple m.Value args} {result : Tuple m.Value outs}
    (ran : Exec m (.project (loops := true) slots) input (some result)) :
    route slots input = result :=
  Option.some.inj (Exec.deterministic .project ran)

theorem Region.run_sound (r : Region localGraph) (fuel : Nat) {input : Tuple m.Value args}
    {output : Tuple m.Value outs} (ran : r.runFuel m fuel input = some output) :
    Exec m r.revert input (some output) := by
  cases r with
  | closed a => exact a.exec_of_runFuel fuel input ran
  | nested a =>
    obtain ⟨value, returned, same⟩ := Option.map_eq_some_iff.mp ran
    obtain ⟨final, executed, readout⟩ := a.returns_of_runFuel fuel fuel returned
    subst output
    rw [← readout]
    exact .seq executed .project

theorem Plan.run_sound (p : Plan g args outs) (fuel : Nat) {input : Tuple m.Value args}
    {output : Tuple m.Value outs} (ran : p.runFuel m fuel input = some output) :
    Exec m p.revert input (some output) := by
  induction p with
  | done slots =>
    have eq := Option.some.inj ran
    subst output
    exact .project
  | step slots stage tail ih =>
    obtain ⟨_, first, second⟩ := Option.bind_eq_some_iff.mp ran
    exact .seq .project (.seq (Region.run_sound stage.region fuel first) (ih second))

private theorem local_forward (r : Region localGraph) (laws : r.Laws m)
    {input : Tuple m.Value args} {output : Tuple m.Value outs} (ran : Exec m r.revert input (some output))
    {localValues : localGraph.Valuation m} (solves : localGraph.Solves m input localValues)
    (i : Index loops) :
    r.Exits m localValues i ∧ localGraph.observe m localValues i = output.map (fun _ => some) := by
  cases r with
  | closed a =>
    have eq := Graph.solves_unique _ m input a.demandWellFounded solves (Graph.denote_solves _ m input a.demandWellFounded)
    rw [eq]
    exact a.firstExit_and_observe_of_exec laws input i ran
  | nested a =>
    have eq := Graph.solves_unique _ m input a.demandWellFounded solves (Graph.denote_solves _ m input a.demandWellFounded)
    rw [eq]
    obtain ⟨final, body, projected⟩ := seq_some ran
    have outEq := project_eq projected
    subst output
    exact a.exits_and_observe_of_returns laws input i ⟨final, body, rfl⟩

private theorem realized_port {refs : Tuple (Ref g.sort) args} {input : Tuple m.Value args}
    {slots : Tuple (Port args) outs} (supplied : Realizes m values refs input) :
    Realizes m values (route slots refs) (route slots input) := by
  intro i t p
  simpa only [route, Simple.get_map] using supplied i t (slots.get p)

theorem parameters_realized {refs : Tuple (Ref g.sort) params}
    (parameters : ParameterRows g refs) (solves : g.Solves m env values) :
    Realizes m values refs env := by
  intro idx t p
  have row := read_node solves (refs.get p) idx
  change Rules.readRef values (refs.get p) idx =
    (nodeAt g (refs.get p)).label.interpret m env idx
      (fun slot j _ => Rules.readRef values ((nodeAt g (refs.get p)).arg slot) j) at row
  rw [parameters t p] at row
  exact row

private theorem output_read (s : Stage g args outs) (base : Index l) (p : Port outs t) :
    (s.graph.observe m (s.pull m values base) (fun k => base (s.keys k))).get p =
      Rules.readRef values (s.output.get p) base := by
  simp only [Graph.observe, Stage.output, Simple.get_map]
  change Rules.readRef (s.pull m values base) (s.graph.roots.get p) (fun k => base (s.keys k)) = _
  rw [read_pull, embedIndex_base]

private theorem stage_forward (s : Stage g args outs)
    {refs : Tuple (Ref g.sort) args} {input : Tuple m.Value args} {output : Tuple m.Value outs}
    (valid : s.Valid refs) (solves : g.Solves m env values) (supplied : Realizes m values refs input)
    (laws : s.region.Laws m) (ran : Exec m s.region.revert input (some output)) :
    (∀ base, s.Exits m values base) ∧ Realizes m values s.output output := by
  have localRun (base : Index l) :=
    local_forward s.region laws ran (pull_solves s valid solves supplied base) (fun k => base (s.keys k))
  refine ⟨fun base => (localRun base).1, fun base t p => ?_⟩
  have atPort := congrArg (fun xs => xs.get p) (localRun base).2
  rw [output_read, Simple.get_map] at atPort
  exact atPort

theorem observations_of_exec (p : Plan g args outs)
    {ins : Tuple (Ref g.sort) args} {out : Tuple (Ref g.sort) outs}
    {input : Tuple m.Value args} {result : Tuple m.Value outs}
    (valid : p.Valid ins out) (solves : g.Solves m env values) (supplied : Realizes m values ins input)
    (laws : p.Laws m) (ran : Exec m p.revert input (some result)) (base : Index l) :
    p.Observations m values base out result := by
  induction p with
  | done slots =>
    have outEq : route slots ins = out := valid
    have resultEq := project_eq ran
    subst out
    subst result
    exact realized_port supplied base
  | step slots stage tail ih =>
    obtain ⟨entry, projected, rest⟩ := seq_some ran
    obtain ⟨next, first, second⟩ := seq_some rest
    have entryEq := project_eq projected
    subst entry
    have valid : stage.Valid (route slots ins) ∧ tail.Valid stage.output out := valid
    have laws : stage.region.Laws m ∧ tail.Laws m := laws
    obtain ⟨exits, seen⟩ := stage_forward stage valid.1 solves (realized_port supplied) laws.1 first
    exact ⟨exits base, next, seen base, ih valid.2 seen laws.2 second⟩

theorem observations_read (p : Plan g args outs) (base : Index l) (out : Tuple (Ref g.sort) outs)
    (result : Tuple m.Value outs) (seen : p.Observations m values base out result) :
    ∀ t (p : Port outs t), Rules.readRef values (out.get p) base = some (result.get p) := by
  induction p with
  | done _ => exact seen
  | step _ _ _ ih => exact ih out result seen.2.choose_spec.2

private theorem tuple_ext {F : Ty Data → Type w}
    (xs ys : Tuple F outs) (same : ∀ t (p : Port outs t), xs.get p = ys.get p) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys => exact congrArg₂ Tuple.cons (same _ .head) (ih ys (fun t p => same t (.tail p)))

theorem observe_of_read (base : Index l) (output : Tuple m.Value results)
    (seen : ∀ t (p : Port results t), Rules.readRef values (g.roots.get p) base = some (output.get p)) :
    g.observe m values base = output.map (fun _ => some) := by
  apply tuple_ext
  intro t p
  simp only [Graph.observe, Simple.get_map]
  exact seen t p

private theorem local_backward (r : Region localGraph) (laws : r.Laws m)
    {input : Tuple m.Value args} {output : Tuple m.Value outs}
    {localValues : localGraph.Valuation m} (solves : localGraph.Solves m input localValues)
    (i : Index loops) (slices : r.Slices m localValues) (exits : r.Exits m localValues i)
    (observed : localGraph.observe m localValues i = output.map (fun _ => some)) :
    Exec m r.revert input (some output) := by
  cases r with
  | closed a =>
    have eq := Graph.solves_unique _ m input a.demandWellFounded solves
      (Graph.denote_solves _ m input a.demandWellFounded)
    rw [eq] at exits observed
    exact (a.exec_iff_firstExit laws slices input i output).mpr ⟨exits, observed⟩
  | nested a =>
    have eq := Graph.solves_unique _ m input a.demandWellFounded solves
      (Graph.denote_solves _ m input a.demandWellFounded)
    rw [eq] at slices exits observed
    obtain ⟨k, exits⟩ := exits
    cases output with
    | cons value rest =>
      cases rest
      obtain ⟨final, ran, same⟩ := a.returns_of_exits laws input slices i exits observed
      rw [← same]
      exact .seq ran .project

theorem exec_of_observations (p : Plan g args outs)
    {ins : Tuple (Ref g.sort) args} {out : Tuple (Ref g.sort) outs}
    {input : Tuple m.Value args} {result : Tuple m.Value outs}
    (valid : p.Valid ins out) (solves : g.Solves m env values) (supplied : Realizes m values ins input)
    (laws : p.Laws m) (base : Index l) (slices : p.Slices m values base)
    (observed : p.Observations m values base out result) :
    Exec m p.revert input (some result) := by
  induction p with
  | done slots =>
    have outEq : route slots ins = out := valid
    subst out
    have projected := realized_port (slots := slots) supplied base
    have same : route slots input = result :=
      tuple_ext _ _ (fun t p => Option.some.inj ((projected t p).symm.trans (observed t p)))
    subst result
    exact .project
  | step slots stage tail ih =>
    obtain ⟨exits, next, seen, remaining⟩ := observed
    have valid : stage.Valid (route slots ins) ∧ tail.Valid stage.output out := valid
    have laws : stage.region.Laws m ∧ tail.Laws m := laws
    have slices : stage.region.Slices m (stage.pull m values base) ∧ tail.Slices m values base := slices
    have entry := realized_port (slots := slots) supplied
    have roots : stage.graph.observe m (stage.pull m values base) (fun k => base (stage.keys k)) =
        next.map (fun _ => some) := by
      apply tuple_ext
      intro t p
      rw [output_read, Simple.get_map]
      exact seen t p
    have first := local_backward stage.region laws.1 (pull_solves stage valid.1 solves entry base)
      _ slices.1 exits roots
    have invariant := (stage_forward stage valid.1 solves entry laws.1 first).2
    exact .seq .project (.seq first (ih valid.2 invariant laws.2 slices.2 remaining))

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Proofs
