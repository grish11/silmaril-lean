module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Thms
public import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
import Silmaril.SSA.PEG.Simple.Revert.While.Region.Total.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Proofs

open RVSDG (Port Tuple)
open Simple.Revert.While.Region (Schedule appendScope nodeAt)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer inner vars extra ins : List (Ty Data)} {result t : Ty Data} {n l : Nat}
variable {g : Graph P outer [result] n l} {m : Interpretation.{u,v,w} P}
variable {input : Tuple m.Value outer} {values : g.Valuation m}

private abbrev read (values : g.Valuation m) (i : Index l) (ref : Ref g.sort t) :=
  Rules.readRef values ref i

private theorem hasNode {r : Ref g.sort t} {label : Label P outer (Fin l) ins t}
    {args : Tuple (Ref g.sort) ins} (eq : nodeAt g r = .ofLabel label args) :
    Rules.HasNode r label args := by
  obtain ⟨i, typed⟩ := r
  cases typed
  exact heq_of_eq eq

private theorem setTwice (i : Index l) (key : Fin l) (j k : Nat) :
    (i.set key j).set key k = i.set key k := by
  funext r
  by_cases h : r = key <;> simp [Index.set, h]

private theorem setCurrent (i : Index l) (key : Fin l) : i.set key (i key) = i := by
  funext r
  by_cases h : r = key <;> simp [Index.set, h]

private theorem setComm (i : Index l) {a b : Fin l} (different : a ≠ b) (j k : Nat) :
    (i.set a j).set b k = (i.set b k).set a j := by
  funext r
  by_cases ha : r = a
  · subst r
    simp [Index.set, different]
  · by_cases hb : r = b
    · subst r
      simp [Index.set, ha]
    · simp [Index.set, ha, hb]

private theorem getLeft {F : Ty Data → Type w} (a : Tuple F vars) (b : Tuple F extra)
    (p : Port vars t) : (appendScope a b).get (portLeft p) = a.get p := by
  induction p with
  | head => cases a; rfl
  | tail _ ih => cases a; exact ih _

private theorem getRight {F : Ty Data → Type w} (a : Tuple F vars) (b : Tuple F extra)
    (p : Port extra t) : (appendScope a b).get (portRight vars p) = b.get p := by
  induction a with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem realizeJoin (i : Index l) (a : Tuple (Ref g.sort) vars)
    (b : Tuple (Ref g.sort) extra) (store : Tuple m.Value (vars ++ extra))
    (left : ∀ t (p : Port vars t), read values i (a.get p) = some (store.get (portLeft p)))
    (right : ∀ t (p : Port extra t), read values i (b.get p) = some (store.get (portRight vars p))) :
    Schedule.Realizes m values i (appendScope a b) store := by
  intro s p
  induction a with
  | nil => exact right s p
  | cons _ _ ih =>
    cases store with
    | cons _ tail =>
      cases p with
      | head => exact left _ .head
      | tail p => exact ih tail (fun t p => left t (.tail p)) right p

private def dropValue : Tuple m.Value (.bool :: vars) → Tuple m.Value vars
  | .cons _ rest => rest

private theorem dropRan (store : Tuple m.Value (.bool :: vars)) :
    (dropFlag vars : Stmt P false _ _).runLoopFree m store = some (dropValue store) := by
  cases store with
  | cons flag tail =>
    change some (((ports vars).map fun _ p => Port.tail p).map
      fun _ p => (Tuple.cons flag tail).get p) = some tail
    apply congrArg some
    have ext {F : Ty Data → Type w} {xs : List (Ty Data)} (a b : Tuple F xs)
        (h : ∀ t (p : Port xs t), a.get p = b.get p) : a = b := by
      induction a with
      | nil => cases b; rfl
      | cons x xs ih =>
        cases b with
        | cons y ys => exact congrArg₂ Tuple.cons (h _ .head) (ih ys fun t p => h t (.tail p))
    apply ext
    intro t p
    rw [get_map, get_map, ports_get]
    rfl

private theorem seqSome {a b c : List (Ty Data)}
    {first : Stmt P true a b} {rest : Stmt P true b c} {old : Tuple m.Value a}
    {final : Tuple m.Value c} (run : Exec m (.seq first rest) old (some final)) :
    ∃ middle, Exec m first old (some middle) ∧ Exec m rest middle (some final) := by
  cases run with
  | seq first rest => exact ⟨_, first, rest⟩

private theorem thetaZero (solves : g.Solves m input values)
    {first next theta : Ref g.sort t} {key : Fin l}
    (wired : nodeAt g theta = .ofLabel (.theta key) (.cons first (.cons next .nil)))
    (base : Index l) :
    read values (base.set key 0) theta = read values (base.set key 0) first :=
  Rules.theta_zero solves (hasNode wired) (by simp [Index.set])

private theorem thetaNext (solves : g.Solves m input values)
    {first next theta : Ref g.sort t} {key : Fin l}
    (wired : nodeAt g theta = .ofLabel (.theta key) (.cons first (.cons next .nil)))
    (base : Index l) (k : Nat) :
    read values (base.set key (k + 1)) theta = read values (base.set key k) next := by
  change Rules.readRef values theta (base.set key (k + 1)) = _
  rw [Rules.theta_succ solves (hasNode wired) (k := k) (by simp [Index.set]), setTwice]

variable {negate : P [.bool] .bool}

private theorem flagOfTest (neg : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {idx : Index l} {tagged : Tuple (Ref g.sort) (.bool :: vars)}
    {store : Tuple m.Value (.bool :: vars)} (entry : Schedule.Realizes m values idx tagged store)
    {b : Bool} (tested : (continueTest negate).eval m store = some ⟨b⟩) :
    (read values idx (tagged.get .head)).map ULift.down = some (!b) := by
  change (Rules.readRef values (tagged.get .head) idx).map ULift.down = _
  rw [entry .bool .head]
  have test := neg (store.get .head).down
  change (continueTest negate).eval m store = _ at test
  have equal := congrArg (ULift.down : ULift.{w} Bool → Bool) (Option.some.inj (test.symm.trans tested))
  change some (store.get .head).down = some (!b)
  change (!(store.get .head).down) = b at equal
  simpa only [Bool.not_not] using congrArg some (congrArg Bool.not equal)

private structure Prefix (tagged : Tuple (Ref g.sort) (.bool :: vars))
    (base : Index l) (key : Fin l) (start count : Nat)
    (final : Tuple m.Value (.bool :: vars)) : Prop where
  last : Schedule.Realizes m values (base.set key (start + count)) tagged final
  stop : (read values (base.set key (start + count)) (tagged.get .head)).map ULift.down = some true
  prior : ∀ j < count,
    (read values (base.set key (start + j)) (tagged.get .head)).map ULift.down = some false
  defined : ∀ j < count, ∀ t (p : Port vars t),
    (read values (base.set key (start + j)) (tagged.get (.tail p))).isSome

private theorem tracePrefix (neg : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (tagged : Tuple (Ref g.sort) (.bool :: vars)) (base : Index l) (key : Fin l)
    {body : Stmt P true (.bool :: vars) (.bool :: vars)}
    (At : Nat → Tuple m.Value (.bool :: vars) → Prop)
    (realize : ∀ {k store}, At k store → Schedule.Realizes m values (base.set key k) tagged store)
    (Event : Nat → Prop)
    (step : ∀ {k old next}, At k old → Exec m body old (some next) → At (k + 1) next ∧ Event k)
    {count : Nat} {store final : Tuple m.Value (.bool :: vars)}
    (trace : WhileTrace m (continueTest negate) body count store final)
    (start : Nat) (entry : At start store) :
    Prefix (values := values) tagged base key start count final ∧
      ∀ j < count, Event (start + j) := by
  induction trace generalizing start with
  | stop test =>
    exact ⟨⟨realize entry, flagOfTest neg (realize entry) test,
      fun j h => (Nat.not_lt_zero j h).elim, fun j h => (Nat.not_lt_zero j h).elim⟩,
      fun j h => (Nat.not_lt_zero j h).elim⟩
  | @step k old next final test body rest ih =>
    obtain ⟨nextAt, event⟩ := step entry body
    obtain ⟨tail, later⟩ := ih (start + 1) nextAt
    have offset (j : Nat) : start + (j + 1) = start + 1 + j := by omega
    refine ⟨⟨by rw [offset]; exact tail.last, by rw [offset]; exact tail.stop, ?_, ?_⟩, ?_⟩
    · intro j lt
      cases j with
      | zero => exact flagOfTest neg (realize entry) test
      | succ j => rw [offset]; exact tail.prior j (by omega)
    · intro j lt s p
      cases j with
      | zero =>
        change (Rules.readRef values (tagged.get (.tail p)) (base.set key start)).isSome
        rw [realize entry s (.tail p)]
        rfl
      | succ j => rw [offset]; exact tail.defined j (by omega) s p
    · intro j lt
      cases j with
      | zero => exact event
      | succ j => rw [offset]; exact later j (by omega)

private theorem passOfPrefix (solves : g.Solves m input values)
    {tagged : Tuple (Ref g.sort) (.bool :: vars)} {base : Index l} {key : Fin l}
    {count : Nat} {final : Tuple m.Value (.bool :: vars)}
    {pass : Ref g.sort .count} (wired : nodeAt g pass = .ofLabel (.pass key) (.cons (tagged.get .head) .nil))
    (facts : Prefix (values := values) tagged base key 0 count final) :
    read values base pass = some ⟨count⟩ := by
  change Rules.readRef values pass base = _
  rw [Rules.pass_at solves (hasNode wired)]
  have first : firstTrue (fun j => (read values (base.set key j) (tagged.get .head)).map ULift.down) =
      some count := (firstTrue_eq_some_iff_samples _ _).mpr
    ⟨by simpa only [Nat.zero_add] using facts.stop,
      fun j hj => by simpa only [Nat.zero_add] using facts.prior j hj⟩
  change (firstTrue (fun j => (read values (base.set key j) (tagged.get .head)).map ULift.down)).map _ = _
  rw [first]
  rfl

private theorem evalOfPrefix (solves : g.Solves m input values)
    {tagged : Tuple (Ref g.sort) (.bool :: vars)} {base : Index l} {key : Fin l}
    {count : Nat} {final : Tuple m.Value (.bool :: vars)}
    {pass : Ref g.sort .count} {root : Ref g.sort t} (p : Port vars t)
    (wired : nodeAt g root = .ofLabel (.eval key)
      (.cons (tagged.get (.tail p)) (.cons pass .nil)))
    (facts : Prefix (values := values) tagged base key 0 count final)
    (picked : read values base pass = some ⟨count⟩) :
    read values base root = some (final.get (.tail p)) := by
  change Rules.readRef values root base = _
  rw [Rules.eval_at solves (hasNode wired)]
  change (read values base pass).elim none
    (fun k => monotonize (fun j => read values (base.set key j) (tagged.get (.tail p))) k.down) = _
  rw [picked]
  change monotonize (fun j => read values (base.set key j) (tagged.get (.tail p))) count = _
  exact (monotonize_eq_some_iff _ _ _).mpr
    ⟨by simpa only [Nat.zero_add] using facts.last t (.tail p),
      fun j hj => by simpa only [Nat.zero_add] using facts.defined j hj t p⟩

private theorem getDrop (store : Tuple m.Value (.bool :: vars)) (p : Port vars t) :
    (dropValue store).get p = store.get (.tail p) := by
  cases store
  rfl

variable (a : Accepted g inner)

private abbrev ChildStore := Tuple m.Value (.bool :: (inner ++ outer))

private theorem withoutFlag {flag : Ref g.sort .bool} {scope : Tuple (Ref g.sort) vars}
    {idx : Index l} {store : Tuple m.Value (.bool :: vars)}
    (entry : Schedule.Realizes m values idx (.cons flag scope) store) :
    Schedule.Realizes m values idx scope (dropValue store) := by
  intro t p
  rw [getDrop]
  exact entry t (.tail p)

private theorem childInitialScope (solves : g.Solves m input values) (base : Index l)
    {old : Tuple m.Value outer} (captures : a.Captures m values base old)
    {initialized : Tuple m.Value (inner ++ outer)}
    (ran : a.childStart.lower.runLoopFree m old = some initialized) :
    Schedule.Realizes m values (base.set a.descriptor.childKey 0) a.descriptor.childScope initialized := by
  have valuesAt := Schedule.realizes_lower a.childStart solves (captures 0) ran
    (idx := base.set a.descriptor.childKey 0)
  apply realizeJoin
  · intro t p
    have initAt := valuesAt t (portLeft p)
    rw [getLeft] at initAt
    exact (thetaZero solves (a.boundary.childTheta t p) base).trans initAt
  · intro t p
    have retained := valuesAt t (portRight inner p)
    rw [getRight] at retained
    exact retained

private theorem childInitial (solves : g.Solves m input values) (base : Index l)
    {old : Tuple m.Value outer} (captures : a.Captures m values base old)
    {start : ChildStore (m := m) (inner := inner) (outer := outer)}
    (ran : a.childStartCode.runLoopFree m old = some start) :
    Schedule.Realizes m values (base.set a.descriptor.childKey 0) a.descriptor.childTagged start := by
  obtain ⟨_, init, guard⟩ := Option.bind_eq_some_iff.mp ran
  exact Schedule.realizes_lower a.childGuard solves (childInitialScope a solves base captures init) guard

private theorem childNextScope (solves : g.Solves m input values) (base : Index l)
    {old : Tuple m.Value outer} (captures : a.Captures m values base old) {k : Nat}
    {store updated : Tuple m.Value (inner ++ outer)}
    (current : Schedule.Realizes m values (base.set a.descriptor.childKey k) a.descriptor.childScope store)
    (ran : a.childStep.lower.runLoopFree m store = some updated) :
    Schedule.Realizes m values (base.set a.descriptor.childKey (k + 1)) a.descriptor.childScope updated := by
  have computed := Schedule.realizes_lower a.childStep solves current ran
  apply realizeJoin
  · intro t p
    have nextAt := computed t (portLeft p)
    rw [getLeft] at nextAt
    exact (thetaNext solves (a.boundary.childTheta t p) base k).trans nextAt
  · intro t p
    have retained := computed t (portRight inner p)
    rw [getRight] at retained
    exact (captures (k + 1) t p).trans ((captures k t p).symm.trans retained)

private theorem childStep (solves : g.Solves m input values) (base : Index l)
    {old : Tuple m.Value outer} (captures : a.Captures m values base old) {k : Nat}
    {store final : ChildStore (m := m) (inner := inner) (outer := outer)}
    (current : Schedule.Realizes m values (base.set a.descriptor.childKey k) a.descriptor.childTagged store)
    (ran : Exec m a.childBody.enableWhile store (some final)) :
    Schedule.Realizes m values (base.set a.descriptor.childKey (k + 1)) a.descriptor.childTagged final := by
  have actual := Exec.deterministic (a.childBody.runLoopFree_enableWhile store) ran
  change ((dropFlag (inner ++ outer)).runLoopFree m store).bind
    (fun old => (a.childStep.lower.runLoopFree m old).bind (a.childGuard.lower.runLoopFree m))
    = some final at actual
  rw [dropRan, Option.bind_some] at actual
  obtain ⟨_, update, guard⟩ := Option.bind_eq_some_iff.mp actual
  exact Schedule.realizes_lower a.childGuard solves
    (childNextScope a solves base captures (withoutFlag current) update) guard

variable (neg : ∀ b : Bool, m.run a.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)

include neg

private theorem childTraceObservation (solves : g.Solves m input values) (base : Index l)
    {old : Tuple m.Value outer} {store final : ChildStore (m := m) (inner := inner) (outer := outer)}
    {k : Nat} (captures : a.Captures m values base old)
    (ranInit : a.childStartCode.runLoopFree m old = some store)
    (trace : WhileTrace m (continueTest a.descriptor.negate) a.childBody.enableWhile k store final) :
    a.ChildObservation m values base k (dropValue final) := by
  have facts := (tracePrefix neg a.descriptor.childTagged base a.descriptor.childKey
    (fun k store => Schedule.Realizes m values (base.set a.descriptor.childKey k) a.descriptor.childTagged store)
    (fun h => h) (fun _ => True)
    (fun entry ran => ⟨childStep a solves base captures entry ran, trivial⟩) trace 0
    (childInitial a solves base captures ranInit)).1
  have pass := passOfPrefix solves a.boundary.childPass facts
  refine ⟨pass, realizeJoin base a.descriptor.childExit a.descriptor.outerTheta _ ?_ ?_⟩
  · intro t p
    rw [getDrop]
    apply evalOfPrefix solves (portLeft p) _ facts pass
    change nodeAt g (a.descriptor.childExit.get p) = .ofLabel (.eval a.descriptor.childKey)
      (.cons (a.descriptor.childScope.get (portLeft p)) (.cons a.descriptor.childPass .nil))
    rw [getLeft]
    exact a.boundary.childExit t p
  · intro t p
    rw [getDrop]
    have retained := facts.last t (.tail (portRight inner p))
    change read values (base.set a.descriptor.childKey (0 + k))
      (a.descriptor.childScope.get (portRight inner p)) = _ at retained
    rw [getRight, Nat.zero_add] at retained
    have atBase := captures (base a.descriptor.childKey) t p
    rw [setCurrent] at atBase
    exact atBase.trans ((captures k t p).symm.trans retained)

theorem activation (solves : g.Solves m input values) (base : Index l)
    {old : Tuple m.Value outer} {out : Tuple m.Value (inner ++ outer)}
    (captures : a.Captures m values base old)
    (ran : Exec m a.activate old (some out)) :
    ∃ k, a.ChildObservation m values base k out := by
  obtain ⟨_, ranInit, rest⟩ := seqSome ran
  obtain ⟨final, ranLoop, projected⟩ := seqSome rest
  obtain ⟨k, trace⟩ := Exec.while_trace ranLoop
  have eq := Exec.deterministic ((dropFlag (inner ++ outer)).runLoopFree_enableWhile final) projected
  rw [dropRan] at eq
  have same := Option.some.inj eq
  subst out
  exact ⟨k, childTraceObservation a neg solves base captures
    (Exec.deterministic (a.childStartCode.runLoopFree_enableWhile old) ranInit) trace⟩

private abbrev OuterStore := Tuple m.Value (.bool :: outer)

private def OuterAt (values : g.Valuation m) (k : Nat) (store : OuterStore (m := m) (outer := outer)) : Prop :=
  ∀ base : Index l, Schedule.Realizes m values (base.set a.descriptor.outerKey k) a.descriptor.outerTagged store

omit neg in
private theorem outerInitialScope (solves : g.Solves m input values) (base : Index l) :
    Schedule.Realizes m values (base.set a.descriptor.outerKey 0) a.descriptor.outerTheta input := by
  intro t p
  change read values (base.set a.descriptor.outerKey 0) (a.descriptor.outerTheta.get p) = _
  rw [thetaZero solves (a.boundary.outerTheta t p) base]
  exact Rules.at_label solves (hasNode (a.boundary.outerInit t p)) _

omit neg in
private theorem outerInitial (solves : g.Solves m input values)
    {store : OuterStore (m := m) (outer := outer)}
    (ran : Exec m a.outerGuard.lower.enableWhile input (some store)) : OuterAt a values 0 store :=
  fun base => Schedule.realizes_lower a.outerGuard solves (outerInitialScope a solves base)
    (Exec.deterministic (a.outerGuard.lower.runLoopFree_enableWhile input) ran)

omit neg in
private theorem outerCaptures {k : Nat} (base : Index l) {store : OuterStore (m := m) (outer := outer)}
    (current : OuterAt a values k store) :
    a.Captures m values (base.set a.descriptor.outerKey k) (dropValue store) := by
  intro j s p
  rw [getDrop, setComm base a.boundary.distinct.symm]
  exact current (base.set a.descriptor.childKey j) s (.tail p)

omit neg in
private theorem outerNextScope (solves : g.Solves m input values) (base : Index l)
    {k trips : Nat} {child : Tuple m.Value (inner ++ outer)} {updated : Tuple m.Value outer}
    (seen : a.ChildObservation m values (base.set a.descriptor.outerKey k) trips child)
    (ran : a.commit.lower.runLoopFree m child = some updated) :
    Schedule.Realizes m values (base.set a.descriptor.outerKey (k + 1)) a.descriptor.outerTheta updated := by
  have next := Schedule.realizes_lower a.commit solves seen.commit ran
  intro s p
  exact (thetaNext solves (a.boundary.outerTheta s p) base k).trans (next s p)

private theorem outerStepFacts (solves : g.Solves m input values) {k : Nat}
    {store final : OuterStore (m := m) (outer := outer)}
    (current : OuterAt a values k store) (ran : Exec m a.body store (some final)) :
    OuterAt a values (k + 1) final ∧
      ∀ base : Index l, ∃ trips, read values (base.set a.descriptor.outerKey k)
        a.descriptor.childPass = some ⟨trips⟩ := by
  obtain ⟨old, dropped, rest⟩ := seqSome ran
  obtain ⟨child, ranChild, rest⟩ := seqSome rest
  obtain ⟨updated, committed, guarded⟩ := seqSome rest
  have eq := Exec.deterministic ((dropFlag outer).runLoopFree_enableWhile store) dropped
  rw [dropRan] at eq
  have same := Option.some.inj eq
  subst old
  have atBase (base : Index l) :
      Schedule.Realizes m values (base.set a.descriptor.outerKey (k + 1)) a.descriptor.outerTagged final ∧
        ∃ trips, read values (base.set a.descriptor.outerKey k) a.descriptor.childPass = some ⟨trips⟩ := by
    obtain ⟨trips, seen⟩ := activation a neg solves (base.set a.descriptor.outerKey k)
      (outerCaptures a base current) ranChild
    have next := outerNextScope a solves base seen
      (Exec.deterministic (a.commit.lower.runLoopFree_enableWhile child) committed)
    exact ⟨Schedule.realizes_lower a.outerGuard solves next
      (Exec.deterministic (a.outerGuard.lower.runLoopFree_enableWhile updated) guarded), trips, seen.pass⟩
  exact ⟨fun base => (atBase base).1, fun base => (atBase base).2⟩

theorem exits_and_observe (solves : g.Solves m input values) (base : Index l)
    {value : m.Value result} (returned : a.revert.Returns m input value) :
    (∃ k, a.FirstExits m values base k) ∧ g.observe m values base = .cons (some value) .nil := by
  obtain ⟨final, ran, out⟩ := returned
  obtain ⟨_, ranInit, ranLoop⟩ := seqSome ran
  obtain ⟨k, trace⟩ := Exec.while_trace ranLoop
  obtain ⟨facts, each⟩ := tracePrefix neg a.descriptor.outerTagged base a.descriptor.outerKey
    (OuterAt a values) (fun h => h base)
    (fun j => ∃ trips, read values (base.set a.descriptor.outerKey j) a.descriptor.childPass = some ⟨trips⟩)
    (fun entry step =>
      let finished := outerStepFacts a neg solves entry step
      ⟨finished.1, finished.2 base⟩)
    trace 0 (outerInitial a solves ranInit)
  have pass := passOfPrefix solves a.boundary.outerPass facts
  have result := evalOfPrefix solves a.descriptor.returnSlot a.boundary.outerExit facts pass
  change final.get (.tail a.descriptor.returnSlot) = value at out
  have singleton : g.roots = .cons (g.roots.get .head) .nil := by
    cases g.roots with | cons _ tail => cases tail; rfl
  have observed : g.observe m values base = Tuple.cons (F := fun ty => Option (m.Value ty))
      (read values base (g.roots.get .head)) .nil := by
    unfold Graph.observe
    rw [singleton]
    rfl
  refine ⟨⟨k, pass, fun j hj => ?_⟩, ?_⟩
  · exact Nat.zero_add j ▸ each j hj
  · rw [observed, result, out]

omit neg

theorem activate_of_runFuel (fuel : Nat) {old : Tuple m.Value outer}
    {out : Tuple m.Value (inner ++ outer)} (ran : a.activateFuel m fuel old = some out) :
    Exec m a.activate old (some out) := by
  obtain ⟨start, started, rest⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨final, loop, returned⟩ := Option.bind_eq_some_iff.mp rest
  exact .seq (started ▸ a.childStartCode.runLoopFree_enableWhile old)
    (.seq (Nested.runWhile_exec (fun h => h ▸ a.childBody.runLoopFree_enableWhile _) fuel loop)
      (returned ▸ (dropFlag (inner ++ outer)).runLoopFree_enableWhile final))

theorem step_of_runFuel (fuel : Nat) {old final : Tuple m.Value (.bool :: outer)}
    (ran : a.stepFuel m fuel old = some final) : Exec m a.body old (some final) := by
  change ((dropFlag outer).runLoopFree m old).bind (fun captured =>
    (a.activateFuel m fuel captured).bind (fun child =>
      (a.commit.lower.runLoopFree m child).bind (a.outerGuard.lower.runLoopFree m))) = _ at ran
  rw [dropRan, Option.bind_some] at ran
  obtain ⟨child, activated, rest⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨updated, committed, guarded⟩ := Option.bind_eq_some_iff.mp rest
  exact .seq (dropRan old ▸ (dropFlag outer).runLoopFree_enableWhile old)
    (.seq (activate_of_runFuel a fuel activated) (.seq
      (committed ▸ a.commit.lower.runLoopFree_enableWhile child)
      (guarded ▸ a.outerGuard.lower.runLoopFree_enableWhile updated)))

theorem returns_of_runFuel (outerFuel childFuel : Nat) {value : m.Value result}
    (ran : a.runFuel m outerFuel childFuel input = some value) :
    a.revert.Returns m input value := by
  obtain ⟨final, loop, returned⟩ := Option.map_eq_some_iff.mp ran
  obtain ⟨start, started, ranLoop⟩ := Option.bind_eq_some_iff.mp loop
  exact ⟨final, .seq (started ▸ a.outerGuard.lower.runLoopFree_enableWhile input)
    (Nested.runWhile_exec (step_of_runFuel a childFuel) outerFuel ranLoop), returned⟩

private theorem flagsOfPass (solves : g.Solves m input values)
    {flag : Ref g.sort .bool} {base : Index l} {key : Fin l}
    {pass : Ref g.sort .count} (wired : nodeAt g pass = .ofLabel (.pass key) (.cons flag .nil))
    {count : Nat} (picked : read values base pass = some ⟨count⟩) :
    (read values (base.set key count) flag).map ULift.down = some true ∧
      ∀ j < count, (read values (base.set key j) flag).map ULift.down = some false := by
  change Rules.readRef values pass base = _ at picked
  rw [Rules.pass_at solves (hasNode wired)] at picked
  apply (firstTrue_eq_some_iff_samples
    (fun j => (read values (base.set key j) flag).map ULift.down) count).mp
  have bare := congrArg (Option.map (ULift.down : ULift.{w} Nat → Nat)) picked
  simpa [Option.map_map, Function.comp_def] using bare

private theorem testOfFlag (neg : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {idx : Index l} {tagged : Tuple (Ref g.sort) (.bool :: vars)}
    {store : Tuple m.Value (.bool :: vars)} (entry : Schedule.Realizes m values idx tagged store)
    {b : Bool} (flag : (read values idx (tagged.get .head)).map ULift.down = some (!b)) :
    (continueTest negate).eval m store = some ⟨b⟩ := by
  have evaluated := neg (store.get .head).down
  change (continueTest negate).eval m store = _ at evaluated
  have actual := flagOfTest neg entry evaluated
  have eq : (!(store.get .head).down) = b := by
    simpa only [Bool.not_not] using congrArg Bool.not (Option.some.inj (actual.symm.trans flag))
  rw [eq] at evaluated
  exact evaluated

/-- Only continuing steps request a transition. The stopping test never
requests a child invocation or a commit. -/
private theorem traceFrom (neg : ∀ b : Bool, m.run negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (tagged : Tuple (Ref g.sort) (.bool :: vars)) (base : Index l) (key : Fin l)
    {body : Stmt P true (.bool :: vars) (.bool :: vars)}
    (At : Nat → Tuple m.Value (.bool :: vars) → Prop)
    (realize : ∀ {k store}, At k store → Schedule.Realizes m values (base.set key k) tagged store)
    (stopAt : Nat) (stop : (read values (base.set key stopAt) (tagged.get .head)).map ULift.down = some true)
    (prior : ∀ j < stopAt, (read values (base.set key j) (tagged.get .head)).map ULift.down = some false)
    (step : ∀ {k old}, k < stopAt → At k old →
      (read values (base.set key k) (tagged.get .head)).map ULift.down = some false →
      ∃ next, Exec m body old (some next) ∧ At (k + 1) next)
    (remaining start : Nat) {store : Tuple m.Value (.bool :: vars)}
    (exactCount : start + remaining = stopAt) (entry : At start store) :
    ∃ final, WhileTrace m (continueTest negate) body remaining store final ∧ At stopAt final := by
  induction remaining generalizing start store with
  | zero =>
    have last : start = stopAt := by omega
    subst start
    exact ⟨store, .stop (testOfFlag neg (realize entry) (b := false) stop), entry⟩
  | succ k ih =>
    have continuing : start < stopAt := by omega
    have flag := prior start continuing
    obtain ⟨next, advanced, nextAt⟩ := step continuing entry flag
    obtain ⟨final, tail, finalAt⟩ := ih (start + 1) (by omega) nextAt
    exact ⟨final, .step (testOfFlag neg (realize entry) (b := true) flag) advanced tail, finalAt⟩

theorem defined_of_total
    (total : ∀ {ins out} (op : P ins out) args, ∃ val, m.run op args = some val) :
    a.DefinedSlices m values :=
  ⟨fun _ store _ => a.outerGuard.lower_total total store,
   fun _ store _ => a.childStart.lower_total total store,
   fun _ store _ => a.childGuard.lower_total total store,
   fun _ store _ _ => a.childStep.lower_total total store,
   fun _ _ store _ => a.commit.lower_total total store⟩

include neg

theorem activate_of_firstExit (solves : g.Solves m input values)
    (slices : a.DefinedSlices m values) (base : Index l) (trips : Nat)
    {old : Tuple m.Value outer} (captures : a.Captures m values base old)
    (picked : Rules.readRef values a.descriptor.childPass base = some ⟨trips⟩) :
    ∃ output, Exec m a.activate old (some output) ∧ a.ChildObservation m values base trips output := by
  obtain ⟨stop, prior⟩ := flagsOfPass solves a.boundary.childPass picked
  obtain ⟨initialized, init⟩ := slices.childStart base old captures
  have initializedAt := childInitialScope a solves base captures init
  obtain ⟨start, guard⟩ := slices.childGuard _ _ initializedAt
  have startAt := Schedule.realizes_lower a.childGuard solves initializedAt guard
  have ranInit : a.childStartCode.runLoopFree m old = some start := by
    change (a.childStart.lower.runLoopFree m old).bind (a.childGuard.lower.runLoopFree m) = _
    rw [init, Option.bind_some, guard]
  let At (k : Nat) (store : ChildStore (m := m) (inner := inner) (outer := outer)) :=
    Schedule.Realizes m values (base.set a.descriptor.childKey k) a.descriptor.childTagged store
  have step {k : Nat} {store : ChildStore (m := m) (inner := inner) (outer := outer)}
      (_ : k < trips) (entry : At k store)
      (again : (read values (base.set a.descriptor.childKey k) a.descriptor.childFlag).map ULift.down =
        some false) : ∃ next, Exec m a.childBody.enableWhile store (some next) ∧ At (k + 1) next := by
    obtain ⟨⟨flag⟩, readFlag, h⟩ := Option.map_eq_some_iff.mp again
    change flag = false at h
    subst flag
    obtain ⟨updated, update⟩ := slices.childStep _ _ (withoutFlag entry) readFlag
    have ready := childNextScope a solves base captures (withoutFlag entry) update
    obtain ⟨next, tested⟩ := slices.childGuard _ _ ready
    exact ⟨next, .seq (dropRan store ▸ (dropFlag (inner ++ outer)).runLoopFree_enableWhile store)
      (.seq (update ▸ a.childStep.lower.runLoopFree_enableWhile (dropValue store))
        (tested ▸ a.childGuard.lower.runLoopFree_enableWhile updated)),
      Schedule.realizes_lower a.childGuard solves ready tested⟩
  obtain ⟨final, trace, _⟩ := traceFrom neg a.descriptor.childTagged base a.descriptor.childKey
    At (fun h => h) trips stop prior step trips 0 (Nat.zero_add trips) startAt
  exact ⟨dropValue final, .seq (ranInit ▸ a.childStartCode.runLoopFree_enableWhile old)
    (.seq trace.exec (dropRan final ▸ (dropFlag (inner ++ outer)).runLoopFree_enableWhile final)),
    childTraceObservation a neg solves base captures ranInit trace⟩

theorem trace_of_exits (solves : g.Solves m input values)
    (slices : a.DefinedSlices m values) (base : Index l) {count : Nat}
    (exits : a.FirstExits m values base count) :
    ∃ start final, Exec m a.outerGuard.lower.enableWhile input (some start) ∧
      WhileTrace m (continueTest a.descriptor.negate) a.body count start final := by
  obtain ⟨stop, prior⟩ := flagsOfPass solves a.boundary.outerPass exits.outer
  obtain ⟨start, init⟩ := slices.outerGuard _ _ (outerInitialScope a solves base)
  have ranInit := init ▸ a.outerGuard.lower.runLoopFree_enableWhile input
  have step {k : Nat} {store : OuterStore (m := m) (outer := outer)}
      (hk : k < count) (entry : OuterAt a values k store)
      (_ : (read values (base.set a.descriptor.outerKey k) a.descriptor.outerFlag).map ULift.down =
        some false) : ∃ next, Exec m a.body store (some next) ∧ OuterAt a values (k + 1) next := by
    obtain ⟨trips, pass⟩ := exits.child k hk
    obtain ⟨child, ranChild, seen⟩ := activate_of_firstExit a neg solves slices
      (base.set a.descriptor.outerKey k) trips (outerCaptures a base entry) pass
    obtain ⟨updated, commit⟩ := slices.commit _ _ _ seen
    have ready := outerNextScope a solves base seen commit
    obtain ⟨next, tested⟩ := slices.outerGuard _ _ ready
    have ran : Exec m a.body store (some next) :=
      .seq (dropRan store ▸ (dropFlag outer).runLoopFree_enableWhile store)
        (.seq ranChild (.seq (commit ▸ a.commit.lower.runLoopFree_enableWhile child)
          (tested ▸ a.outerGuard.lower.runLoopFree_enableWhile updated)))
    exact ⟨next, ran, (outerStepFacts a neg solves entry ran).1⟩
  obtain ⟨final, trace, _⟩ := traceFrom neg a.descriptor.outerTagged base a.descriptor.outerKey
    (OuterAt a values) (fun h => h base) count stop prior step count 0 (Nat.zero_add count)
    (outerInitial a solves ranInit)
  exact ⟨start, final, ranInit, trace⟩

theorem returns_of_exits (solves : g.Solves m input values)
    (slices : a.DefinedSlices m values) (base : Index l) {count : Nat}
    (exits : a.FirstExits m values base count) {value : m.Value result}
    (observed : g.observe m values base = .cons (some value) .nil) :
    a.revert.Returns m input value := by
  obtain ⟨_, final, started, trace⟩ := trace_of_exits a neg solves slices base exits
  have ran : a.revert.Returns m input (final.get (.tail a.descriptor.returnSlot)) :=
    ⟨final, .seq started trace.exec, rfl⟩
  have seen := (exits_and_observe a neg solves base ran).2.symm.trans observed
  have picked := congrArg (fun xs : Tuple (fun t => Option (m.Value t)) [result] => xs.get .head) seen
  exact ⟨final, .seq started trace.exec, Option.some.inj picked⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Region.Proofs
