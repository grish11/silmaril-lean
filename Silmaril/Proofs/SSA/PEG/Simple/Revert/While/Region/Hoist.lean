module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
public import Silmaril.SSA.PEG.Figure19.Placement.MustEval.Thms
public import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Rows

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Proofs

open RVSDG (Port Tuple)
open Region.Proofs (clock read)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars larger ins outs : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1} {m : Interpretation.{u,v,w} P}
variable {env : Tuple m.Value carried} {values : g.Valuation m}

private theorem tuple_ext {F : Ty Data → Type w} (a b : Tuple F vars)
    (h : ∀ s (p : Port vars s), a.get p = b.get p) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons x xs ih =>
    cases b with
    | cons y ys => exact congrArg₂ Tuple.cons (h _ .head) (ih ys fun s p => h s (.tail p))

private theorem select (store : Tuple m.Value vars) (other : Tuple m.Value larger)
    (embed : Embedding vars larger) (agrees : ∀ s (p : Port vars s), other.get (embed p) = store.get p) :
    ((ports vars).map fun _ p => embed p).map (fun _ p => other.get p) = store := by
  apply tuple_ext
  intro s p
  rw [get_map, get_map, ports_get]
  exact agrees s p

private theorem args_eval {scope : Tuple (Ref g.sort) vars} {refs : Tuple (Ref g.sort) ins}
    (reads : Region.Reads scope refs) (store : Tuple m.Value vars) (other : Tuple m.Value larger)
    (embed : Embedding vars larger) (agrees : ∀ s (p : Port vars s), other.get (embed p) = store.get p) :
    (Reads.rebasedArgs embed reads).eval m other = reads.args.eval m store := by
  induction reads with
  | nil => rfl
  | cons p _ tail ih =>
    simp only [Reads.rebasedArgs, Region.Reads.args, Args.eval, Expr.evalLift, agrees, ih]

private theorem retain_eval {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (code : Schedule g false roots scope) (store : Tuple m.Value vars) (other : Tuple m.Value larger)
    (embed : Embedding vars larger) (cache : Port larger t)
    (agrees : ∀ s (p : Port vars s), other.get (embed p) = store.get p) :
    (retain code embed cache).runLoopFree m other =
      (code.lower.runLoopFree m store).map (Tuple.cons (other.get cache)) := by
  induction code generalizing larger with
  | done reads =>
    change some (Tuple.cons (other.get cache)
      ((reads.slots.map fun _ p => embed p).map fun _ p => other.get p)) =
      some (Tuple.cons (other.get cache) (reads.slots.map fun _ p => store.get p))
    congr 2
    apply tuple_ext
    intro s p
    rw [get_map, get_map, get_map, agrees]
  | bind i op refs fresh row reads tail ih =>
    have h := args_eval reads store other embed agrees
    simp only [retain, Schedule.lower, Stmt.runLoopFree, Expr.eval, Expr.evalLift, h]
    cases result : (reads.args.eval m store).elim none (m.run op) with
    | none => rfl
    | some value =>
      simp only [Option.map_some, Option.bind_some]
      exact ih (Tuple.cons value store) (Tuple.cons value other) _ (.tail cache)
        (fun s p => match p with | .head => rfl | .tail q => agrees s q)
  | branch impossible => nomatch impossible

private def paramSafe {sort : Fin n → Ty Data} (node : Node P carried (Fin 1) sort t) : Prop :=
  isParam node → node.label.thetaLoop ≠ some 0 ∧ node.inputs.length = 0

private theorem paramSafe_all {sort : Fin n → Ty Data} (node : Node P carried (Fin 1) sort t) :
    paramSafe node := by
  obtain ⟨ins, label, args⟩ := node
  cases label <;> simp [paramSafe, isParam, Label.thetaLoop]

private theorem param_invariant {i : Fin n} (p : isParam (g.node i)) : Rules.InvariantAt g 0 i := by
  obtain ⟨theta, arity⟩ := paramSafe_all (g.node i) p
  refine Rules.invariantAt_iff.mpr ⟨theta, ?_⟩
  rintro b kind ⟨⟨slot, _, _⟩, _⟩
  exact (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le slot.isLt (Nat.le_of_eq arity))).elim

theorem invariantAt {d : Descriptor g} {i : Fin n} (site : Site d i) : Rules.InvariantAt g 0 i := by
  apply Rules.invariantAt_iff.mpr
  constructor
  · have eq := congrArg (fun node => node.label.thetaLoop) site.row
    change (g.node i).label.thetaLoop = none at eq
    rw [eq]
    intro h
    cases h
  · rintro j kind ⟨edge, _⟩
    let depends (node : Node P carried (Fin 1) g.sort (g.sort i)) :=
      ∃ slot : Fin node.inputs.length, node.label.kind slot = kind ∧ (node.arg slot).id = j
    change depends (g.node i) at edge
    rw [site.row] at edge
    obtain ⟨slot, _, rfl⟩ := edge
    exact param_invariant (site.params slot)

theorem cache_of_defined {d : Descriptor g} {i : Fin n} (site : Site d i)
    (wf : WellFounded g.Demand) (solves : g.Solves m env values) (idx : Index 1)
    (ready : (values ((d.next.get (portAt carried site.updateSlot)).id, idx)).isSome) :
    ∃ cache : m.Value (g.sort i), ∀ atIndex,
      Rules.readRef values (Ref.ofId g.sort i) atIndex = some cache := by
  have hit := Figure19.MustEval.defined solves n site.demanded ready
  obtain ⟨cache, hc⟩ := Option.isSome_iff_exists.mp hit
  refine ⟨cache, fun atIndex => ?_⟩
  have invariant := Rules.invariant_sound wf solves (r := Ref.ofId g.sort i) (invariantAt site)
  rw [invariant atIndex idx (fun k hk => (hk (Subsingleton.elim k 0)).elim)]
  exact hc

variable (a : Accepted g)

private abbrev Tagged := Tuple m.Value (.bool :: carried)
private abbrev At (values : g.Valuation m) (k : Nat) (store : Tagged (m := m) (carried := carried)) :=
  Region.Proofs.Realizes values (clock k) a.descriptor.guardRoots store

private def old (store : Tuple m.Value (.bool :: carried)) : Tuple m.Value carried :=
  match store with | .cons _ xs => xs

private theorem old_at {k : Nat} {store : Tagged (m := m) (carried := carried)}
    (atState : At a values k store) :
    Region.Proofs.Realizes values (clock k) a.descriptor.theta (old store) := by
  cases store with
  | cons flag store => exact fun t p => atState t (.tail p)

private theorem primitive_eq (solves : g.Solves m env values) {k : Nat}
    {store : Tagged (m := m) (carried := carried)} (entry : At a values k store) :
    (Expr.op a.site.instr a.site.reads.args).eval m (old store) =
      read values (clock k) (Ref.ofId g.sort a.shared) := by
  have h := Region.Proofs.row solves (clock k) (Ref.ofId g.sort a.shared)
  let rhs (node : Node P carried (Fin 1) g.sort (g.sort a.shared)) :=
    node.label.interpret m env (clock k) fun j idx _ => read values idx (node.arg j)
  change read values (clock k) (Ref.ofId g.sort a.shared) = rhs (g.node a.shared) at h
  rw [a.site.row] at h
  change read values (clock k) (Ref.ofId g.sort a.shared) =
    (collect _ (fun j => read values (clock k) (a.site.operands.get (portAt _ j)))).elim
      none (m.run a.site.instr) at h
  rw [Region.Proofs.operands a.site.reads (old_at a entry)] at h
  exact h.symm

private theorem body_base (store : Tagged (m := m) (carried := carried)) :
    a.base.body.runLoopFree m store =
      ((Expr.op a.site.instr a.site.reads.args).eval m (old store)).bind fun cache =>
        (a.rest.lower.runLoopFree m (.cons cache (old store))).bind (a.guard.lower.runLoopFree m) := by
  unfold Accepted.base Certificate.body
  have proj := select (old store) store (fun p => .tail p) (by cases store; intros; rfl)
  simp only [Stmt.runLoopFree, Schedule.lower, proj, Option.bind_some]
  cases (Expr.op a.site.instr a.site.reads.args).eval m (old store) <;> rfl

private theorem initialize_eq (solves : g.Solves m env values) {k : Nat}
    {store : Tagged (m := m) (carried := carried)} (entry : At a values k store)
    {cache : m.Value (g.sort a.shared)}
    (aligned : read values (clock k) (Ref.ofId g.sort a.shared) = some cache) :
    a.initialize.runLoopFree m store = some (.cons cache store) := by
  have args := args_eval a.site.reads (old store) store (fun p => .tail p)
    (by cases store; intros; rfl)
  have computed := (primitive_eq a solves entry).trans aligned
  change ((a.site.reads.args.eval m (old store)).elim none (m.run a.site.instr)) = _ at computed
  simp only [Accepted.initialize, Stmt.runLoopFree, Expr.eval, Expr.evalLift, args, computed, Option.map_some]

private theorem cached_body (cache : m.Value (g.sort a.shared))
    (store : Tagged (m := m) (carried := carried)) :
    a.body.runLoopFree m (.cons cache store) =
      ((a.rest.lower.runLoopFree m (.cons cache (old store))).bind
        (a.guard.lower.runLoopFree m)).map (Tuple.cons cache) := by
  have proj := select (old store) (.cons cache store) (fun p => .tail (.tail p))
    (by cases store; intros; rfl)
  simp only [Accepted.body, Stmt.runLoopFree, Tuple.map, Tuple.get, proj, Option.bind_some]
  rw [retain_eval a.rest _ _ _ _ (fun _ _ => rfl)]
  cases ran : a.rest.lower.runLoopFree m (.cons cache (old store)) with
  | none => rfl
  | some next =>
    simp only [Option.map_some, Option.bind_some]
    exact retain_eval a.guard next (.cons cache next) (fun p => .tail p) .head (fun _ _ => rfl)

private theorem read_isSome (r : Ref g.sort t) {idx : Index 1} :
    (read values idx r).isSome = (values (r.id, idx)).isSome := by
  obtain ⟨id, typed⟩ := r
  subst t
  rfl

private theorem step_ready {k : Nat} {store next : Tagged (m := m) (carried := carried)}
    (solves : g.Solves m env values) (entry : At a values k store)
    (ran : a.base.body.runLoopFree m store = some next) :
    (values ((a.descriptor.next.get (portAt carried a.site.updateSlot)).id, clock k)).isSome ∧
      At a values (k + 1) next := by
  rw [body_base] at ran
  obtain ⟨cache, expr, tail⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨updated, updateRan, guardRan⟩ := Option.bind_eq_some_iff.mp tail
  have aligned : read values (clock k) (Ref.ofId g.sort a.shared) = some cache :=
    (primitive_eq a solves entry).symm.trans expr
  have realized : Region.Proofs.Realizes values (clock k) (.cons (Ref.ofId g.sort a.shared) a.descriptor.theta)
      (.cons cache (old store)) := by
    intro t p
    cases p with
    | head => exact aligned
    | tail p => exact old_at a entry _ p
  have updatedAt := Region.Proofs.schedule a.rest solves realized updateRan
  have sampled := updatedAt _ (portAt carried a.site.updateSlot)
  refine ⟨?_, Region.Proofs.schedule a.guard solves (Region.Proofs.update a.base solves updatedAt) guardRan⟩
  exact read_isSome _ ▸ (Option.isSome_iff_exists.mpr ⟨_, sampled⟩)

private theorem trace_cached (solves : g.Solves m env values)
    {cache : m.Value (g.sort a.shared)}
    (aligned : ∀ k, read values (clock k) (Ref.ofId g.sort a.shared) = some cache)
    {steps : Nat} {store final : Tagged (m := m) (carried := carried)}
    (trace : WhileTrace m (.var .head) a.base.body.enableWhile steps store final) (k : Nat)
    (entry : At a values k store) :
    WhileTrace m (.var (.tail .head)) a.body.enableWhile steps (.cons cache store) (.cons cache final) := by
  induction trace generalizing k with
  | stop test => exact .stop test
  | @step steps store next final test body rest ih =>
    have ran := Exec.deterministic (a.base.body.runLoopFree_enableWhile store) body
    have advance := (step_ready a solves entry ran).2
    rw [body_base, (primitive_eq a solves entry).trans (aligned k), Option.bind_some] at ran
    have out : a.body.runLoopFree m (.cons cache store) = some (.cons cache next) := by
      rw [cached_body, ran, Option.map_some]
    exact .step test (out ▸ a.body.runLoopFree_enableWhile _) (ih (k + 1) advance)

theorem returns_of_trace (solves : g.Solves m env values) {steps : Nat}
    {start final : Tuple m.Value (.bool :: carried)}
    (guard : a.guard.lower.runLoopFree m env = some start)
    (trace : WhileTrace m (.var .head) a.base.body.enableWhile steps start final) :
    a.revert.Returns m env (final.get (.tail a.descriptor.returnSlot)) := by
  have init := Region.Proofs.schedule a.guard solves (Region.Proofs.initial a.base solves) guard
  have first := guard ▸ a.guard.lower.runLoopFree_enableWhile env
  cases trace with
  | stop test =>
    refine ⟨old start, .seq first (.branchFalse test ?_), ?_⟩
    · have eq := select (old start) start (fun p => .tail p) (by cases start; intros; rfl)
      exact eq ▸ Exec.project
    · cases start; rfl
  | @step k start next final test step rest =>
    have ran := Exec.deterministic (a.base.body.runLoopFree_enableWhile start) step
    obtain ⟨cache, everywhere⟩ := cache_of_defined a.site a.base.demandWellFounded solves _
      (step_ready a solves init ran).1
    have initialized := initialize_eq a solves init (everywhere (clock 0))
    have replay := trace_cached a solves (fun k => everywhere (clock k))
      (.step test step rest) 0 init
    refine ⟨old final, .seq first (.branchTrue test
      (.seq (initialized ▸ a.initialize.runLoopFree_enableWhile start) (.seq replay.exec ?_))), ?_⟩
    · have eq := select (old final) (.cons cache final) (fun p => .tail (.tail p))
        (by cases final; intros; rfl)
      exact eq ▸ Exec.project
    · cases final; rfl


theorem returns_of_returns {value : m.Value result} (ran : a.base.revert.Returns m env value) :
    a.revert.Returns m env value := by
  obtain ⟨final, exec, returned⟩ := ran
  change Exec m (.seq a.guard.lower.enableWhile (.while rfl (.var .head) a.base.body.enableWhile))
    env (some final) at exec
  cases exec with
  | seq first loop =>
    obtain ⟨k, trace⟩ := Exec.while_trace loop
    have guard := Exec.deterministic (a.guard.lower.runLoopFree_enableWhile env) first
    change final.get (.tail a.descriptor.returnSlot) = value at returned
    exact returned ▸ returns_of_trace a (g.denote_solves m env a.base.demandWellFounded) guard trace

private theorem runCached_trace (fuel : Nat)
    (store : Tuple m.Value (g.sort a.shared :: .bool :: carried))
    {value : m.Value result} (ran : a.runCached m fuel store = some value) :
    ∃ k final, WhileTrace m (.var (.tail .head)) a.body.enableWhile k store final ∧
      final.get (.tail (.tail a.descriptor.returnSlot)) = value := by
  induction fuel generalizing store with
  | zero =>
    cases store with | cons cache tagged =>
    cases tagged with | cons flag old =>
    obtain ⟨flag⟩ := flag
    cases flag
    · exact ⟨0, _, .stop rfl, Option.some.inj ran⟩
    · cases ran
  | succ k ih =>
    cases store with | cons cache tagged =>
    cases tagged with | cons flag old =>
    obtain ⟨flag⟩ := flag
    cases flag
    · exact ⟨0, _, .stop rfl, Option.some.inj ran⟩
    · change (a.body.runLoopFree m (.cons cache (.cons ⟨true⟩ old))).bind (a.runCached m k) =
        some value at ran
      obtain ⟨next, ranBody, ranTail⟩ := Option.bind_eq_some_iff.mp ran
      obtain ⟨length, final, trace, returned⟩ := ih next ranTail
      exact ⟨length + 1, final,
        .step rfl (ranBody ▸ a.body.runLoopFree_enableWhile _) trace, returned⟩

theorem runFuel_returns (fuel : Nat) {value : m.Value result}
    (ran : a.runFuel m fuel env = some value) : a.revert.Returns m env value := by
  cases guard : a.guard.lower.runLoopFree m env with
  | none => simp [Accepted.runFuel, guard] at ran
  | some store =>
    cases store with | cons flag xs =>
    obtain ⟨flag⟩ := flag
    have first := guard ▸ a.guard.lower.runLoopFree_enableWhile env
    cases flag
    · simp only [Accepted.runFuel, guard, Tuple.get] at ran
      change some (xs.get a.descriptor.returnSlot) = some value at ran
      refine ⟨xs, .seq first (.branchFalse rfl ?_), Option.some.inj ran⟩
      have projected := Exec.project (model := m) (loops := true)
        (slots := (ports carried).map fun _ p => .tail p)
        (store := Tuple.cons (F := m.Value) (t := Ty.bool) ⟨false⟩ xs)
      rw [select xs _ (fun p => .tail p) (fun _ _ => rfl)] at projected
      exact projected
    · simp only [Accepted.runFuel, guard, Tuple.get, ite_eq_left True.intro] at ran
      cases init : a.initialize.runLoopFree m (.cons ⟨true⟩ xs) with
      | none => simp [init] at ran
      | some cached =>
        rw [init] at ran
        obtain ⟨_, final, trace, returned⟩ := runCached_trace a fuel cached ran
        refine ⟨_, .seq first (.branchTrue rfl
          (.seq (init ▸ a.initialize.runLoopFree_enableWhile _) (.seq trace.exec .project))), ?_⟩
        change (((ports carried).map fun _ p => .tail (.tail p)).map
          (fun _ p => final.get p)).get a.descriptor.returnSlot = value
        rw [get_map, get_map, ports_get]
        exact returned

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist.Proofs
