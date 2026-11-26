module

public import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Rows
public import Silmaril.SSA.PEG.Simple.While.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1} {m : Interpretation.{u,v,w} P}
variable {env : Tuple m.Value carried} {values : g.Valuation m}
variable (cert : Certificate g)

abbrev Tagged (m : Interpretation.{u,v,w} P) (carried : List (Ty Data)) :=
  Tuple m.Value (.bool :: carried)

abbrev Trace (cert : Certificate g) (m : Interpretation.{u,v,w} P) :=
  WhileTrace m (.var .head) cert.body.enableWhile

private abbrev At (k : Nat) (tagged : Tagged m carried) :=
  Realizes values (clock k) cert.descriptor.guardRoots tagged

private def projectOld (tagged : Tagged m carried) : Tuple m.Value carried :=
  ((ports carried).map fun _ p => RVSDG.Port.tail p).map fun _ p => tagged.get p

private theorem runBody (tagged : Tagged m carried) :
    cert.body.runLoopFree m tagged =
      (cert.update.lower.runLoopFree m (projectOld tagged)).bind (cert.guard.lower.runLoopFree m) :=
  rfl

private theorem bodyTotal (total : cert.Total m) (tagged : Tagged m carried) :
    ∃ next, cert.body.runLoopFree m tagged = some next := by
  obtain ⟨next, updated⟩ := total.update (projectOld tagged)
  obtain ⟨taggedNext, tested⟩ := total.guard next
  exact ⟨taggedNext, by rw [runBody, updated]; exact tested⟩

private theorem start (solves : g.Solves m env values) {tagged : Tagged m carried}
    (ran : cert.guard.lower.runLoopFree m env = some tagged) : At cert (values := values) 0 tagged :=
  schedule cert.guard solves (initial cert solves) ran

private theorem advance (solves : g.Solves m env values) {i : Nat} {tagged next : Tagged m carried}
    (entry : At cert (values := values) i tagged)
    (ran : Exec m cert.body.enableWhile tagged (some next)) :
    At cert (values := values) (i + 1) next := by
  have computed := Exec.deterministic (cert.body.runLoopFree_enableWhile tagged) ran
  rw [runBody] at computed
  obtain ⟨updated, updates, guard⟩ := Option.bind_eq_some_iff.mp computed
  have old : Realizes values (clock i) cert.descriptor.theta (projectOld tagged) := by
    intro t p
    unfold projectOld
    rw [get_map, get_map, ports_get]
    exact entry t (.tail p)
  exact schedule cert.guard solves (update cert solves (schedule cert.update solves old updates)) guard

variable (solves : g.Solves m env values)
variable (neg : ∀ b : Bool, m.run cert.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)

include solves neg

private theorem flagAt {i : Nat} {tagged : Tagged m carried}
    (atEntry : At cert (values := values) i tagged)
    {b : Bool} (test : (Expr.var (.head : RVSDG.Port (.bool :: carried) .bool) : Expr P _ _).eval
      m tagged = some ⟨b⟩) :
    flags cert values i = some (!b) := by
  have guard : read values (clock i) cert.descriptor.guard = some ⟨b⟩ :=
    (atEntry .bool .head).trans test
  unfold flags
  rw [exitFlag cert solves neg guard]
  rfl

private theorem testOfFlag {i : Nat} {tagged : Tagged m carried}
    (atEntry : At cert (values := values) i tagged)
    {b : Bool} (test : flags cert values i = some (!b)) :
    (Expr.var (.head : RVSDG.Port (.bool :: carried) .bool) : Expr P _ _).eval m tagged = some ⟨b⟩ := by
  cases tagged with
  | cons value store =>
    obtain ⟨actual⟩ := value
    have h := flagAt cert solves neg atEntry (b := actual) rfl
    rw [h] at test
    cases actual <;> cases b <;> simp_all <;> rfl

private structure Prefix (i k : Nat) (final : Tagged m carried) : Prop where
  last : At cert (values := values) (i + k) final
  stop : flags cert values (i + k) = some true
  earlier : ∀ j < k, flags cert values (i + j) = some false
  defined : ∀ j < k, (samples cert values (i + j)).isSome

private theorem tracePrefix {k : Nat} {tagged final : Tagged m carried}
    (trace : Trace cert m k tagged final) (i : Nat) (entry : At cert (values := values) i tagged) :
    Prefix (values := values) cert i k final := by
  induction trace generalizing i with
  | stop test =>
    exact ⟨entry, flagAt cert solves neg entry test, fun j h => (Nat.not_lt_zero j h).elim,
      fun j h => (Nat.not_lt_zero j h).elim⟩
  | @step k tagged next final test body rest ih =>
    have after := ih (i + 1) (advance cert solves entry body)
    have offset (j : Nat) : i + (j + 1) = i + 1 + j := by omega
    refine ⟨by rw [offset]; exact after.last, by rw [offset]; exact after.stop, ?_, ?_⟩
    · intro j lt
      cases j with
      | zero => exact flagAt cert solves neg entry test
      | succ j => rw [offset]; exact after.earlier j (by omega)
    · intro j lt
      cases j with
      | zero =>
        change (samples cert values i).isSome
        unfold samples
        have sample := entry result (.tail cert.descriptor.returnSlot)
        rw [Descriptor.guardRoots, Tuple.get] at sample
        rw [sample]
        rfl
      | succ j => rw [offset]; exact after.defined j (by omega)

private theorem traceOfFlags (total : cert.Total m)
    (i k : Nat) {tagged : Tagged m carried} (entry : At cert (values := values) i tagged)
    (stop : flags cert values (i + k) = some true)
    (again : ∀ j < k, flags cert values (i + j) = some false) :
    ∃ final, Trace cert m k tagged final ∧ At cert (values := values) (i + k) final := by
  induction k generalizing i tagged with
  | zero => exact ⟨tagged, .stop (testOfFlag cert solves neg entry (b := false) stop), entry⟩
  | succ k ih =>
    have test := testOfFlag cert solves neg entry (b := true) (again 0 (Nat.zero_lt_succ _))
    obtain ⟨next, computed⟩ := bodyTotal cert total tagged
    have ran := computed ▸ cert.body.runLoopFree_enableWhile tagged
    have offset (j : Nat) : i + 1 + j = i + (j + 1) := by omega
    obtain ⟨final, rest, last⟩ := ih (i + 1) (advance cert solves entry ran)
      (by rw [offset]; exact stop)
      (fun j hj => by rw [offset]; exact again (j + 1) (by omega))
    exact ⟨final, .step test ran rest, by rw [← offset]; exact last⟩

omit solves neg in
private theorem unpack {value : m.Value result} (success : cert.revert.Returns m env value) :
    ∃ k tagged final, cert.guard.lower.runLoopFree m env = some tagged ∧
      Trace cert m k tagged final ∧ final.get (.tail cert.descriptor.returnSlot) = value := by
  obtain ⟨final, ran, returned⟩ := success
  change Exec m (.seq cert.guard.lower.enableWhile (.while rfl (.var .head) cert.body.enableWhile))
    env (some final) at ran
  cases ran with
  | seq first rest =>
    obtain ⟨k, trace⟩ := Exec.while_trace rest
    exact ⟨k, _, final, Exec.deterministic (cert.guard.lower.runLoopFree_enableWhile env) first,
      trace, returned⟩

theorem observe_of_returns (i : Index 1) {value : m.Value result}
    (success : cert.revert.Returns m env value) :
    g.observe m values i = .cons (some value) .nil := by
  obtain ⟨k, tagged, final, guard, trace, returned⟩ := unpack cert success
  have ran := tracePrefix cert solves neg trace 0 (start cert solves guard)
  have first : firstTrue (flags cert values) = some k :=
    (firstTrue_eq_some_iff_samples _ _).mpr
      ⟨by simpa only [Nat.zero_add] using ran.stop,
        fun j hj => by simpa only [Nat.zero_add] using ran.earlier j hj⟩
  rw [observation cert solves, pass cert solves, first]
  change Tuple.cons (F := fun t => Option (m.Value t)) (monotonize (samples cert values) k) .nil = _
  congr 1
  apply (monotonize_eq_some_iff _ _ _).mpr
  have sample := (ran.last result (.tail cert.descriptor.returnSlot)).trans (congrArg some returned)
  exact ⟨by simpa only [samples, Nat.zero_add, Descriptor.guardRoots, Tuple.get] using sample,
    fun j hj => by simpa only [Nat.zero_add] using ran.defined j hj⟩

theorem exitWitness_of_defined (total : cert.Total m) (i : Index 1)
    {value : m.Value result} (defined : g.observe m values i = .cons (some value) .nil) :
    ∃ k tagged final, cert.guard.lower.runLoopFree m env = some tagged ∧
      cert.ExitWitness m values i k tagged final value := by
  rw [observation cert solves] at defined
  have observed := congrArg (fun xs : Tuple (fun t => Option (m.Value t)) [result] =>
    xs.get .head) defined
  change (read values i cert.descriptor.pass).elim none
    (fun k => monotonize (samples cert values) k.down) = some value at observed
  rw [pass cert solves] at observed
  cases first : firstTrue (flags cert values) with
  | none => rw [first] at observed; cases observed
  | some k =>
    rw [first] at observed
    obtain ⟨sample, earlier⟩ := (monotonize_eq_some_iff _ _ _).mp observed
    obtain ⟨stop, again⟩ := (firstTrue_eq_some_iff_samples _ _).mp first
    obtain ⟨tagged, tested⟩ := total.guard env
    obtain ⟨final, trace, last⟩ := traceOfFlags cert solves neg total 0 k
      (start cert solves tested)
      (by simpa only [Nat.zero_add] using stop)
      (fun j hj => by simpa only [Nat.zero_add] using again j hj)
    have atExit : samples cert values k = some (final.get (.tail cert.descriptor.returnSlot)) := by
      simpa only [samples, Nat.zero_add, Descriptor.guardRoots, Tuple.get] using
        last result (.tail cert.descriptor.returnSlot)
    have picked : read values i cert.descriptor.pass = some ⟨k⟩ := by
      rw [pass cert solves, first]
      rfl
    exact ⟨k, tagged, final, tested, trace, Option.some.inj (atExit.symm.trans sample),
      picked, sample, earlier⟩

omit solves neg

theorem returns_of_exit {k : Nat} {tagged final : Tagged m carried} {i : Index 1}
    {value : m.Value result} (guard : cert.guard.lower.runLoopFree m env = some tagged)
    (witness : cert.ExitWitness m values i k tagged final value) :
    cert.revert.Returns m env value :=
  ⟨final, .seq (guard ▸ cert.guard.lower.runLoopFree_enableWhile env) witness.trace.exec,
    witness.returned⟩

private theorem runFrom_trace {k : Nat} {tagged final : Tagged m carried}
    (trace : Trace cert m k tagged final) :
    cert.runFrom m k tagged = some (final.get (.tail cert.descriptor.returnSlot)) := by
  induction trace with
  | @stop tagged test =>
    cases tagged with
    | cons flag store =>
      have h : flag = ⟨false⟩ := Option.some.inj test
      subst flag
      rfl
  | @step k tagged next final test step rest ih =>
    cases tagged with
    | cons flag store =>
      have h : flag = ⟨true⟩ := Option.some.inj test
      subst flag
      have computed := Exec.deterministic (cert.body.runLoopFree_enableWhile _) step
      simpa [Certificate.runFrom, computed] using ih

theorem runFuel_of_exit {k : Nat} {tagged final : Tagged m carried} {i : Index 1}
    {value : m.Value result} (guard : cert.guard.lower.runLoopFree m env = some tagged)
    (witness : cert.ExitWitness m values i k tagged final value) :
    cert.runFuel m k env = some value := by
  unfold Certificate.runFuel
  rw [guard]
  exact (runFrom_trace cert witness.trace).trans (congrArg some witness.returned)

private theorem runFrom_success (fuel : Nat) (tagged : Tagged m carried) {value : m.Value result}
    (ran : cert.runFrom m fuel tagged = some value) :
    ∃ final, Exec m (.while rfl (.var .head) cert.body.enableWhile) tagged (some final) ∧
      final.get (.tail cert.descriptor.returnSlot) = value := by
  induction fuel generalizing tagged with
  | zero =>
    cases tagged with
    | cons flag store =>
      obtain ⟨flag⟩ := flag
      cases flag
      · exact ⟨_, .whileStop rfl, Option.some.inj ran⟩
      · cases ran
  | succ k ih =>
    cases tagged with
    | cons flag store =>
      obtain ⟨flag⟩ := flag
      cases flag
      · exact ⟨_, .whileStop rfl, Option.some.inj ran⟩
      · change (cert.body.runLoopFree m (.cons ⟨true⟩ store)).bind (cert.runFrom m k) =
          some value at ran
        obtain ⟨next, computed, rest⟩ := Option.bind_eq_some_iff.mp ran
        obtain ⟨final, loop, returned⟩ := ih next rest
        exact ⟨final, .whileStep rfl (computed ▸ cert.body.runLoopFree_enableWhile _) loop, returned⟩

theorem runFuel_returns (fuel : Nat) {value : m.Value result}
    (ran : cert.runFuel m fuel env = some value) : cert.revert.Returns m env value := by
  obtain ⟨tagged, guard, rest⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨final, loop, returned⟩ := runFrom_success cert fuel tagged rest
  exact ⟨final, .seq (guard ▸ cert.guard.lower.runLoopFree_enableWhile env) loop, returned⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Proofs
