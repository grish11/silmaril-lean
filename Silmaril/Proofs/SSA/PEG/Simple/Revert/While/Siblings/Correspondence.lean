module

public import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Siblings.Transport
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Proofs

open RVSDG (Port Tuple)
open Simple.Revert.While.Region

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params intermediate args results carried₁ carried₂ ps outs : List (Ty Data)}
variable {n n₁ n₂ rows : Nat} {t : Ty Data}
variable {g : Graph P params results n 2}
variable {left : Graph P params intermediate n₁ 1} {right : Graph P args results n₂ 1}
variable {first : Closed.Accepted left carried₁} {second : Closed.Accepted right carried₂}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params} {values : g.Valuation m}

private theorem seq_some {xs ys zs : List (Ty Data)}
    {a : Stmt P true xs ys} {b : Stmt P true ys zs}
    {input : Tuple m.Value xs} {output : Tuple m.Value zs}
    (ran : Exec m (.seq a b) input (some output)) :
    ∃ mid, Exec m a input (some mid) ∧ Exec m b mid (some output) := by
  cases ran with | seq first second => exact ⟨_, first, second⟩

private theorem input_params (d : Layout g left right) (valid : Boundary d)
    (solves : g.Solves m env values) (idx : Index 2) (t : Ty Data) (p : Port params t) :
    Rules.readRef values (d.inputs.get p) idx = some (env.get p) := by
  have node : Rules.HasNode (d.inputs.get p) (.param p) .nil := by
    have eq := valid.inputs t p
    generalize d.inputs.get p = ref at eq ⊢
    obtain ⟨i, typed⟩ := ref
    cases typed
    exact heq_of_eq eq
  exact Rules.at_label solves node idx

private theorem input_handoff (d : Layout g left right)
    {mid : Tuple m.Value intermediate}
    (seen : ∀ idx, observeRefs m g values idx d.firstRoots = mid.map (fun _ => some))
    (idx : Index 2) (t : Ty Data) (p : Port args t) :
    Rules.readRef values (d.rightInputs.get p) idx = some ((d.handoff m mid).get p) := by
  have atPort := congrArg (fun xs => xs.get (d.route.get p)) (seen idx)
  simp only [observeRefs, Simple.get_map] at atPort
  simpa only [Layout.rightInputs, Layout.handoff, Simple.get_map] using atPort

private theorem stage_transport {stage : Graph P ps outs rows 1}
    (addresses : Addresses stage.sort g.sort) (bindings : Tuple (Ref g.sort) ps)
    (base : Index 2) (key : Fin 2)
    (matched : ∀ i, Matches g stage key addresses bindings i)
    (solves : g.Solves m env values) {input : Tuple m.Value ps}
    (supplied : ∀ (i : Index 2) t (p : Port ps t),
      Rules.readRef values (bindings.get p) i = some (input.get p))
    (wf : WellFounded stage.Demand) :
    (∀ t (r : Ref stage.sort t),
      Rules.readRef (stage.denote m input wf) r (fun _ => base key) =
        Rules.readRef values (push addresses r) base) ∧
    stage.observe m (stage.denote m input wf) (fun _ => base key) =
      observeRefs m g values base (stage.roots.map fun _ => push addresses) := by
  rw [denote_pull addresses bindings base key matched solves supplied wf]
  constructor
  · intro t r
    rw [read_pull, atStage_current]
  · rw [observe_pull, atStage_current]

variable (a : Accepted g first second)

private theorem left_observations (solves : g.Solves m env values) (laws : first.Laws m)
    {mid : Tuple m.Value intermediate} (ran : Exec m first.revert env (some mid))
    (idx : Index 2) :
    (∃ k, Rules.readRef values (push a.layout.first first.descriptor.pass) idx = some ⟨k⟩) ∧
    observeRefs m g values idx a.layout.firstRoots = mid.map (fun _ => some) := by
  have localRun := first.firstExit_and_observe_of_exec laws env (fun _ => idx 0) ran
  have transfer := stage_transport a.layout.first a.layout.inputs idx 0 a.boundary.first solves
    (input_params a.layout a.boundary solves) first.demandWellFounded
  obtain ⟨⟨k, pass⟩, roots⟩ := localRun
  exact ⟨⟨k, (transfer.1 .count first.descriptor.pass).symm.trans pass⟩, transfer.2.symm.trans roots⟩

theorem observations_of_exec (solves : g.Solves m env values)
    (laws₁ : first.Laws m) (laws₂ : second.Laws m) (idx : Index 2)
    {output : Tuple m.Value results} (ran : Exec m a.revert env (some output)) :
    ∃ mid, a.Observations m values idx mid output := by
  obtain ⟨mid, ranFirst, rest⟩ := seq_some ran
  obtain ⟨in₂, projected, ranSecond⟩ := seq_some rest
  have same := Option.some.inj (Exec.deterministic
    (Exec.project (slots := a.layout.route) (store := mid)) projected)
  change a.layout.handoff m mid = in₂ at same
  subst in₂
  have seen (i : Index 2) := left_observations a solves laws₁ ranFirst i
  have localRun := second.firstExit_and_observe_of_exec laws₂ _ (fun _ => idx 1) ranSecond
  have transfer := stage_transport a.layout.second a.layout.rightInputs idx 1 a.boundary.second solves
    (input_handoff a.layout (fun i => (seen i).2)) second.demandWellFounded
  obtain ⟨⟨k, pass⟩, roots⟩ := localRun
  have final := transfer.2.symm.trans roots
  change observeRefs m g values idx a.layout.secondRoots = _ at final
  rw [a.boundary.output] at final
  exact ⟨mid, (seen idx).1, ⟨k, (transfer.1 .count second.descriptor.pass).symm.trans pass⟩,
    (seen idx).2, final⟩

theorem exec_of_runFuel (fuel₁ fuel₂ : Nat) {output : Tuple m.Value results}
    (ran : a.runFuel m fuel₁ fuel₂ env = some output) : Exec m a.revert env (some output) := by
  obtain ⟨mid, one, two⟩ := Option.bind_eq_some_iff.mp ran
  exact .seq (first.exec_of_runFuel fuel₁ env one)
    (.seq .project (second.exec_of_runFuel fuel₂ (a.layout.handoff m mid) two))

theorem runFuel_of_observations (solves : g.Solves m env values)
    (laws₁ : first.Laws m) (laws₂ : second.Laws m)
    (total₁ : first.Total m) (total₂ : second.Total m) (idx : Index 2)
    {mid : Tuple m.Value intermediate} {output : Tuple m.Value results}
    (observed : a.Observations m values idx mid output) :
    ∃ fuel₁ fuel₂, a.runFuel m fuel₁ fuel₂ env = some output := by
  obtain ⟨k₁, pass₁⟩ := observed.firstExit
  have transfer₁ := stage_transport a.layout.first a.layout.inputs idx 0 a.boundary.first solves
    (input_params a.layout a.boundary solves) first.demandWellFounded
  have ran₁ := first.runFuel_of_firstExit laws₁ total₁ env (fun _ => idx 0) k₁
    ((transfer₁.1 .count first.descriptor.pass).trans pass₁) (transfer₁.2.trans observed.first)
  have seen (i : Index 2) := (left_observations a solves laws₁
    (first.exec_of_runFuel k₁ env ran₁) i).2
  obtain ⟨k₂, pass₂⟩ := observed.secondExit
  have transfer₂ := stage_transport a.layout.second a.layout.rightInputs idx 1 a.boundary.second solves
    (input_handoff a.layout seen) second.demandWellFounded
  have obs₂ : observeRefs m g values idx a.layout.secondRoots = output.map (fun _ => some) := by
    rw [a.boundary.output]
    exact observed.second
  have ran₂ := second.runFuel_of_firstExit laws₂ total₂ (a.layout.handoff m mid) (fun _ => idx 1) k₂
    ((transfer₂.1 .count second.descriptor.pass).trans pass₂) (transfer₂.2.trans obs₂)
  exact ⟨k₁, k₂, by simpa only [Accepted.runFuel, ran₁, Option.bind_some] using ran₂⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Proofs
