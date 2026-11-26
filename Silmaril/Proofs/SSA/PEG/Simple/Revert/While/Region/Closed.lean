module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
public import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Rows

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Proofs

open RVSDG (Port Tuple)
open Region.Proofs (clock setClock)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params carried results vars ins more : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P params results n 1} {m : Interpretation.{u,v,w} P}
variable {values : g.Valuation m} {input : Tuple m.Value params}

private abbrev read (values : g.Valuation m) (idx : Index 1) (ref : Ref g.sort t) :=
  Rules.readRef values ref idx

private theorem tuple_ext {F : Ty Data → Type w} (a b : Tuple F vars)
    (get : ∀ s (p : Port vars s), a.get p = b.get p) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons x xs ih =>
    cases b with
    | cons y ys => exact congrArg₂ Tuple.cons (get _ .head) (ih ys fun s p => get s (.tail p))

private theorem hasNode {r : Ref g.sort t} {label : Label P params (Fin 1) ins t}
    {args : Tuple (Ref g.sort) ins} (eq : nodeAt g r = .ofLabel label args) :
    Rules.HasNode r label args := by
  obtain ⟨i, typed⟩ := r
  cases typed
  exact heq_of_eq eq

private theorem get_left {F : Ty Data → Type w} (left : Tuple F vars) (right : Tuple F more)
    (p : Port vars t) : (appendScope left right).get (portLeft p) = left.get p := by
  induction p with
  | head => cases left; rfl
  | tail p ih => cases left; exact ih _

private theorem get_right {F : Ty Data → Type w} (left : Tuple F vars) (right : Tuple F more)
    (p : Port more t) : (appendScope left right).get (portRight vars p) = right.get p := by
  induction left with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem realizes_append {result : Ty Data}
    {view : Graph P params [result] n 1} {valuation : view.Valuation m}
    (idx : Index 1) (left : Tuple (Ref view.sort) vars)
    (right : Tuple (Ref view.sort) more) (store : Tuple m.Value (vars ++ more))
    (leftAt : ∀ t (p : Port vars t),
      Region.Proofs.read valuation idx (left.get p) = some (store.get (portLeft p)))
    (rightAt : ∀ t (p : Port more t),
      Region.Proofs.read valuation idx (right.get p) = some (store.get (portRight vars p))) :
    Region.Proofs.Realizes (g := view) valuation idx (appendScope left right) store := by
  intro s p
  induction left with
  | nil => exact rightAt s p
  | cons r rs ih =>
    cases store with
    | cons v vs =>
      cases p with
      | head => exact leftAt _ .head
      | tail p => exact ih vs (fun t p => leftAt t (.tail p)) rightAt p

variable (a : Accepted g carried)

private abbrev Tagged := Tuple m.Value a.storeTypes

private def old (store : Tagged a (m := m)) : Tuple m.Value (carried ++ a.captures.types) :=
  match store with | .cons _ xs => xs

private theorem old_eq (store : Tagged a (m := m)) :
    ((oldSlots (carried ++ a.captures.types)).map fun _ p => store.get p) = old a store := by
  apply tuple_ext
  intro s p
  rw [get_map, oldSlots, get_map, ports_get]
  cases store
  rfl

private abbrev At (values : g.Valuation m) (k : Nat) (store : Tagged a (m := m)) :=
  Region.Proofs.Realizes (g := a.descriptor.view) values (clock k)
    (appendScope a.descriptor.tagged a.captures.refs) store ∧
    store.get (portLeft (.tail a.descriptor.clock)) = ⟨k⟩

private theorem parameter (solves : g.Solves m input values) (idx : Index 1)
    (p : Port a.captures.types t) :
    read values idx (a.captures.refs.get p) = some (input.get (a.captures.inputs.get p)) := by
  rw [Parameters.refs, Parameters.inputs, get_map, get_map]
  change Region.Proofs.read (g := a.descriptor.view) values idx (a.captures.bindings.get p).ref = _
  rw [Region.Proofs.row solves, (a.captures.bindings.get p).wired]
  rfl

private theorem initial (laws : a.Laws m) (solves : g.Solves m input values)
    {start : Tagged a (m := m)}
    (ran : a.startCode.runLoopFree m input = some start) : At a values 0 start := by
  let captured := a.captures.inputs.map fun _ p => input.get p
  change (a.start.lower.runLoopFree m captured).bind (a.guard.lower.runLoopFree m) = some start at ran
  obtain ⟨initial, ranInit, guard⟩ := Option.bind_eq_some_iff.mp ran
  have base := Region.Proofs.schedule a.start solves
    (fun _ p => by rw [get_map]; exact parameter a solves (clock 0) p) ranInit (idx := clock 0)
  have theta (s : Ty Data) (p : Port carried s) :
      read (g := g) values (clock 0) (a.descriptor.theta.get p) = some (initial.get (portLeft p)) := by
    have init := base s (portLeft p)
    rw [get_left] at init
    exact (Rules.theta_zero solves (hasNode (a.boundary.theta s p)) rfl).trans init
  have entry := realizes_append (view := a.descriptor.view) (valuation := values) (clock 0) a.descriptor.theta a.captures.refs initial theta
    (fun s p => by
      have h := base s (portRight carried p)
      rw [get_right] at h
      exact h)
  have zero := Region.Proofs.row (g := a.descriptor.view) solves (clock 0)
    (a.descriptor.initial.get a.descriptor.clock)
  change read (g := g) values (clock 0) (a.descriptor.initial.get a.descriptor.clock) =
    (let node := nodeAt g (a.descriptor.initial.get a.descriptor.clock)
     node.label.interpret m input (clock 0) fun slot j _ => read (g := g) values j (node.arg slot)) at zero
  rw [a.boundary.zero] at zero
  change _ = m.run a.descriptor.zero .nil at zero
  have tagged := Region.Proofs.schedule a.guard solves entry guard
  have startClock := tagged .count (portLeft (.tail a.descriptor.clock))
  rw [get_left] at startClock
  exact ⟨tagged, Option.some.inj
    (startClock.symm.trans ((Rules.theta_zero solves (hasNode (a.boundary.theta _ _)) rfl).trans
      (zero.trans laws.zero)))⟩

private theorem advance (laws : a.Laws m) (solves : g.Solves m input values)
    {k : Nat} {store final : Tagged a (m := m)} (current : At a values k store)
    (step : Exec m a.body.enableWhile store (some final)) : At a values (k + 1) final := by
  have ran := Exec.deterministic (a.body.runLoopFree_enableWhile store) step
  change ((some ((oldSlots (carried ++ a.captures.types)).map fun _ p => store.get p)).bind fun old =>
    (a.step.lower.runLoopFree m old).bind (a.guard.lower.runLoopFree m)) = some final at ran
  rw [old_eq, Option.bind_some] at ran
  obtain ⟨next, ranStep, ranGuard⟩ := Option.bind_eq_some_iff.mp ran
  have before : Region.Proofs.Realizes (g := a.descriptor.view) values (clock k)
      (appendScope a.descriptor.theta a.captures.refs) (old a store) := by
    cases store with | cons flag xs => exact fun s p => current.1 s (.tail p)
  have update := Region.Proofs.schedule a.step solves before ranStep
  have theta (s : Ty Data) (p : Port carried s) :
      read (g := g) values (clock (k + 1)) (a.descriptor.theta.get p) = some (next.get (portLeft p)) := by
    rw [read, Rules.theta_succ solves (hasNode (a.boundary.theta s p)) (i := clock (k + 1))
      (k := k) rfl, setClock]
    have h := update s (portLeft p)
    rw [get_left] at h
    exact h
  have entry := realizes_append (view := a.descriptor.view) (valuation := values) (clock (k + 1)) a.descriptor.theta a.captures.refs next theta
    (fun s p => by
      have h := update s (portRight carried p)
      rw [get_right] at h
      exact (parameter a solves _ p).trans ((parameter a solves _ p).symm.trans h))
  have clockBefore := current.1 .count (portLeft (.tail a.descriptor.clock))
  rw [get_left, current.2] at clockBefore
  change read values (clock k) (a.descriptor.theta.get a.descriptor.clock) = _ at clockBefore
  have tick := Rules.unary_at solves (hasNode a.boundary.tick) (clock k)
  change read (g := g) values (clock k) (a.descriptor.next.get a.descriptor.clock) =
    (read (g := g) values (clock k) (a.descriptor.theta.get a.descriptor.clock)).bind _ at tick
  rw [clockBefore, Option.bind_some, laws.tick] at tick
  have tagged := Region.Proofs.schedule a.guard solves entry ranGuard
  have finalClock := tagged .count (portLeft (.tail a.descriptor.clock))
  rw [get_left] at finalClock
  change read values (clock (k + 1)) (a.descriptor.theta.get a.descriptor.clock) = _ at finalClock
  refine ⟨tagged, Option.some.inj (finalClock.symm.trans ?_)⟩
  rw [read, Rules.theta_succ solves (hasNode (a.boundary.theta _ _)) (i := clock (k + 1))
    (k := k) rfl, setClock]
  exact tick

private def flags (values : g.Valuation m) (k : Nat) : Option Bool :=
  (read (g := g) values (clock k) a.descriptor.exit).map ULift.down

private theorem flag (laws : a.Laws m) {k : Nat} {store : Tagged a (m := m)}
    (atStore : At a values k store) {b : Bool}
    (test : a.test.eval m store = some ⟨b⟩) : flags a values k = some (!b) := by
  have existsFlag := atStore.1 .bool (portLeft .head)
  rw [get_left] at existsFlag
  change read (g := g) values (clock k) a.descriptor.exit = some (store.get .head) at existsFlag
  unfold flags
  rw [existsFlag]
  have testEq : m.run a.descriptor.negate (.cons (store.get .head) .nil) = some ⟨b⟩ := test
  have inv := laws.negate (store.get .head).down
  have eq : (!(store.get .head).down) = b := congrArg ULift.down (Option.some.inj (inv.symm.trans testEq))
  rw [← eq]
  simp

private structure Prefix (values : g.Valuation m) (offset k : Nat)
    (final : Tagged a (m := m)) : Prop where
  finalAt : At a values (offset + k) final
  stop : flags a values (offset + k) = some true
  before : ∀ j < k, flags a values (offset + j) = some false
  defined : ∀ j < k, ∀ s (p : Port carried s),
    (read (g := g) values (clock (offset + j)) (a.descriptor.theta.get p)).isSome

private theorem trace_prefix (laws : a.Laws m) (solves : g.Solves m input values)
    {start final : Tagged a (m := m)} {k : Nat}
    (trace : WhileTrace m a.test a.body.enableWhile k start final)
    (i : Nat) (entry : At a values i start) : Prefix a values i k final := by
  induction trace generalizing i with
  | stop test =>
    exact ⟨entry, flag a laws entry test, fun j lt => (Nat.not_lt_zero j lt).elim,
      fun j lt => (Nat.not_lt_zero j lt).elim⟩
  | @step k start next final test step rest ih =>
    have tail := ih (i + 1) (advance a laws solves entry step)
    have same (j : Nat) : i + (j + 1) = i + 1 + j := by omega
    refine ⟨by rw [same]; exact tail.finalAt, by rw [same]; exact tail.stop, ?_, ?_⟩
    · intro j lt
      cases j with
      | zero => exact flag a laws entry test
      | succ j => rw [same]; exact tail.before j (by omega)
    · intro j lt s p
      cases j with
      | zero =>
        have defined := entry.1 s (portLeft (.tail p))
        rw [get_left] at defined
        change read (g := g) values (clock i) (a.descriptor.theta.get p) = _ at defined
        rw [Nat.add_zero, defined]
        rfl
      | succ j => rw [same]; exact tail.defined j (by omega) s p

private theorem pass_read (solves : g.Solves m input values) (idx : Index 1) :
    read (g := g) values idx a.descriptor.pass = (firstTrue (flags a values)).map ULift.up := by
  rw [read, Rules.pass_at solves (hasNode a.boundary.pass) idx]
  unfold flags
  simp only [setClock]

private theorem readout (solves : g.Solves m input values) (idx : Index 1) {k : Nat}
    {final : Tagged a (m := m)} (facts : Prefix a values 0 k final)
    (pass : read (g := g) values idx a.descriptor.pass = some ⟨k⟩)
    (root : Ref g.sort t) (out : Readout carried t) (wired : a.descriptor.rootRow root out) :
    read (g := g) values idx root = some (final.get (portLeft (a.descriptor.slot out))) := by
  cases out with
  | pass =>
    change root = a.descriptor.pass at wired
    have count := facts.finalAt.2
    rw [Nat.zero_add] at count
    change read (g := g) values idx root = some (final.get (portLeft (.tail a.descriptor.clock)))
    rw [wired, pass, count]
  | eval port =>
    change Rules.readRef values a.descriptor.pass idx = some ⟨k⟩ at pass
    rw [read, Rules.eval_at solves (hasNode wired) idx, pass]
    change monotonize (fun j =>
      read (g := g) values (idx.set 0 j) (a.descriptor.theta.get port)) k =
        some (final.get (portLeft (.tail port)))
    simp only [setClock]
    apply (monotonize_eq_some_iff _ _ _).mpr
    have last := facts.finalAt.1 _ (portLeft (.tail port))
    rw [get_left] at last
    change read values (clock (0 + k)) (a.descriptor.theta.get port) = _ at last
    exact ⟨by simpa only [Nat.zero_add] using last,
      fun j hj => by simpa only [Nat.zero_add] using facts.defined j hj _ port⟩

private theorem seq_some {loops : Bool} {middle : List (Ty Data)}
    {first : Stmt P loops vars middle} {second : Stmt P loops middle more}
    {store : Tuple m.Value vars} {output : Tuple m.Value more}
    (ran : Exec m (.seq first second) store (some output)) :
    ∃ mid, Exec m first store (some mid) ∧ Exec m second mid (some output) := by
  cases ran with
  | seq before after => exact ⟨_, before, after⟩

theorem observe_of_exec (laws : a.Laws m) (solves : g.Solves m input values) (idx : Index 1)
    {output : Tuple m.Value results} (ran : Exec m a.revert input (some output)) :
    g.observe m values idx = output.map (fun _ => some) := by
  change Exec m (.seq a.startCode.enableWhile
    (.seq (.while rfl a.test a.body.enableWhile) a.finishCode.enableWhile)) input (some output) at ran
  obtain ⟨_, start, rest⟩ := seq_some ran
  obtain ⟨final, loop, finish⟩ := seq_some rest
  obtain ⟨k, trace⟩ := Exec.while_trace loop
  have facts := trace_prefix a laws solves trace 0
    (initial a laws solves (Exec.deterministic (a.startCode.runLoopFree_enableWhile input) start))
  have first : firstTrue (flags a values) = some k :=
    (firstTrue_eq_some_iff_samples _ _).mpr ⟨by simpa only [Nat.zero_add] using facts.stop,
      fun j hj => by simpa only [Nat.zero_add] using facts.before j hj⟩
  have pass : read (g := g) values idx a.descriptor.pass = some ⟨k⟩ := by
    rw [pass_read a solves, first]
    rfl
  have ranFinish := Exec.deterministic (a.finishCode.runLoopFree_enableWhile final) finish
  let projected := a.exitSlots.map fun _ p => final.get p
  change a.finish.lower.runLoopFree m projected = some output at ranFinish
  have entry := realizes_append (view := a.descriptor.view) (valuation := values) idx
    a.descriptor.sampleRefs a.captures.refs (a.exitSlots.map fun _ p => final.get p) (fun s p => by
      rw [get_map, Accepted.exitSlots, get_left, get_map, Descriptor.slots, get_map]
      exact readout a solves idx facts pass _ _ (a.boundary.outputs s p))
    (fun s p => by
      rw [get_map, Accepted.exitSlots, get_right, get_map, ports_get]
      have captured := facts.finalAt.1 s (.tail (portRight carried p))
      change read values (clock (0 + k))
        ((appendScope a.descriptor.theta a.captures.refs).get (portRight carried p)) = _ at captured
      rw [get_right, parameter a solves] at captured
      exact (parameter a solves idx p).trans captured)
  have returned := Region.Proofs.schedule a.finish solves entry ranFinish
  apply tuple_ext
  intro s p
  rw [Graph.observe, get_map, get_map]
  exact returned s p

theorem exec_of_runFuel (fuel : Nat) {output : Tuple m.Value results}
    (ran : a.runFuel m fuel input = some output) : Exec m a.revert input (some output) := by
  have loop {fuel : Nat} {start : Tagged a (m := m)}
      (ran : a.runFrom m fuel start = some output) :
      Exec m (.seq (.while rfl a.test a.body.enableWhile) a.finishCode.enableWhile)
        start (some output) := by
    suffices ∃ final, Exec m (.while rfl a.test a.body.enableWhile) start (some final) ∧
        a.finishCode.runLoopFree m final = some output by
      obtain ⟨final, ranLoop, returned⟩ := this
      exact .seq ranLoop (returned ▸ a.finishCode.runLoopFree_enableWhile final)
    induction fuel generalizing start with
    | zero =>
      rw [Accepted.runFrom] at ran
      cases flag : a.test.eval m start with
      | none => simp [flag] at ran
      | some value =>
        obtain ⟨b⟩ := value
        cases b
        · exact ⟨start, .whileStop flag, by simpa [flag] using ran⟩
        · simp [flag] at ran
    | succ k ih =>
      rw [Accepted.runFrom] at ran
      cases flag : a.test.eval m start with
      | none => simp [flag] at ran
      | some value =>
        obtain ⟨b⟩ := value
        cases b
        · exact ⟨start, .whileStop flag, by simpa [flag] using ran⟩
        · rw [flag] at ran
          change (a.body.runLoopFree m start).bind (a.runFrom m k) = some output at ran
          obtain ⟨next, step, remaining⟩ := Option.bind_eq_some_iff.mp ran
          obtain ⟨final, trace, returned⟩ := ih remaining
          exact ⟨final, .whileStep flag (step ▸ a.body.runLoopFree_enableWhile start) trace, returned⟩
  obtain ⟨start, initialized, remaining⟩ := Option.bind_eq_some_iff.mp ran
  exact .seq (initialized ▸ a.startCode.runLoopFree_enableWhile input) (loop remaining)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Proofs
