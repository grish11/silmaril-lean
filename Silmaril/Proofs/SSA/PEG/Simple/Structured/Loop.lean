module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Views
public import Silmaril.SSA.PEG.Simple.While.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w x y

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before vars inside all : List (Ty Data)} {t : Ty Data}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params} {read : Reads m all}
variable {active : List (Fin all.length)}
variable {init : Tuple (Port before) vars} {body : Code P params (vars ++ before) inside}
variable {guard : Port inside .bool} {next : Tuple (Port inside) vars} {neg : P [.bool] .bool}
variable (view : View m env read active (.loop init body guard next neg))

private theorem atOuter {i fixed : Index all.length} {k : Nat}
    (h : Agrees (view.key :: active) (fixed.set view.key k) i) : Agrees active fixed i := by
  intro l member
  have eq := h l (List.mem_cons_of_mem _ member)
  rwa [Index.set, ite_eq_right (view.key_fresh member)] at eq

private theorem atKey {i fixed : Index all.length} {k : Nat}
    (h : Agrees (view.key :: active) (fixed.set view.key k) i) : i view.key = k := by
  have eq := h view.key (List.mem_cons_self)
  simpa [Index.set] using eq

theorem sampleAgrees {i fixed : Index all.length} (h : Agrees active fixed i) (k : Nat) :
    Agrees (view.key :: active) (fixed.set view.key k) (i.set view.key k) := by
  intro l member
  rcases List.mem_cons.mp member with rfl | outer
  · simp [Index.set]
  · simp only [Index.set, ite_eq_right (view.key_fresh outer), h l outer]

/-- The body sees the source store in its θ slots, uniformly at all indices
with the same enclosing coordinates and this loop's iteration. -/
@[expose] def AtIteration (fixed : Index all.length) (k : Nat) (store : Tuple m.Value vars) : Prop :=
  RealizesOn read (fun r => view.inner.embed (body.lift r))
    ((ports vars).map fun _ r => portLeft r) store (view.key :: active) (fixed.set view.key k)

private theorem slotAt {fixed j : Index all.length} {k : Nat} {store : Tuple m.Value vars}
    (h : AtIteration view fixed k store) (atJ : Agrees (view.key :: active) (fixed.set view.key k) j)
    {t : Ty Data} (slot : Port vars t) :
    read (view.inner.embed (body.lift (portLeft slot))) j = some (store.get slot) := by
  have eq := h j atJ _ slot
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get] at eq
  exact eq

private theorem thetaEquation {t : Ty Data} (slot : Port vars t) (j : Index all.length) :
    read (view.inner.embed (body.lift (portLeft slot))) j =
      rowValue m env
        ⟨_, .theta view.key,
          .cons (view.inner.embed (body.lift (portRight vars (init.get slot))))
            (.cons (view.inner.embed (next.get slot)) .nil), none⟩ read j := by
  have h := view.inner.eqs j t (body.lift (portLeft slot))
  change _ = rowValue m env
    (body.rows (loopHoles body init next view.holes view.embed) (fun r => view.inner.embed r)
      (some view.key) (body.lift (portLeft slot))) read j at h
  rw [rows_lift, loopHoles_left] at h
  exact h

private theorem thetaZero {t : Ty Data} (slot : Port vars t) (j : Index all.length)
    (zero : j view.key = 0) :
    read (view.inner.embed (body.lift (portLeft slot))) j =
      read (view.inner.embed (body.lift (portRight vars (init.get slot)))) j := by
  refine (thetaEquation view slot j).trans ?_
  simp only [rowValue, Label.interpret]
  generalize eq : j view.key = count at zero ⊢
  clear eq
  subst count
  rfl

private theorem thetaNext {t : Ty Data} (slot : Port vars t) (j : Index all.length) (k : Nat)
    (tick : j view.key = k + 1) :
    read (view.inner.embed (body.lift (portLeft slot))) j =
      read (view.inner.embed (next.get slot)) (j.set view.key k) := by
  refine (thetaEquation view slot j).trans ?_
  simp only [rowValue, Label.interpret]
  generalize eq : j view.key = count at tick ⊢
  clear eq
  subst count
  rfl

theorem atEntry {fixed : Index all.length} {store : Tuple m.Value vars}
    (entry : RealizesOn read (fun r => view.embed ((Code.loop init body guard next neg).lift r))
      init store active fixed) : AtIteration view fixed 0 store := by
  intro j atJ t slot
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact (thetaZero view slot j (atKey view atJ)).trans (entry j (atOuter view atJ) t slot)

theorem stepIteration {fixed : Index all.length} {k : Nat} {store : Tuple m.Value vars}
    (h : RealizesOn read view.inner.embed next store (view.key :: active) (fixed.set view.key k)) :
    AtIteration view fixed (k + 1) store := by
  intro j atJ t slot
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact (thetaNext view slot j k (atKey view atJ)).trans
    (h _ (sampleAgrees view (atOuter view atJ) k) t slot)

private theorem collectOne (r : (i : Fin [Ty.bool].length) → Option (m.Value [Ty.bool][i])) :
    collect [.bool] r = (r 0).map (fun b => Tuple.cons b .nil) := by
  unfold collect
  cases r 0 <;> rfl

theorem exitTestExact (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (j : Index all.length) :
    read (view.embed (negRef vars)) j =
      (read (view.inner.embed guard) j).map (fun flag => ⟨!flag.down⟩) := by
  refine (view.eqs j _ (negRef vars)).trans ?_
  change rowValue m env (loopRows body guard neg active.head? view.embed
    (body.rows view.inner.holes view.inner.embed (some view.key)) (negRef vars)) read j = _
  rw [loopRows_neg]
  change (collect (F := m.Value) [.bool] _).elim none (m.run neg) = _
  rw [collectOne]
  change ((read (view.inner.embed guard) j).map (fun x => .cons x .nil)).elim none (m.run neg) = _
  cases read (view.inner.embed guard) j with
  | none => rfl
  | some flag => exact negSem flag.down

private theorem exitTest (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (j : Index all.length) {flag : Bool} (guardValue : read (view.inner.embed guard) j = some ⟨flag⟩) :
    read (view.embed (negRef vars)) j = some ⟨!flag⟩ := by
  rw [exitTestExact view negSem, guardValue]
  rfl

structure Exits (fixed : Index all.length) (start count : Nat) (final : Tuple m.Value vars) : Prop where
  store : AtIteration view fixed (start + count) final
  stop : ∀ j, Agrees active fixed j →
    read (view.embed (negRef vars)) (j.set view.key (start + count)) = some ⟨true⟩
  prior : ∀ k < count, ∀ j, Agrees active fixed j →
    read (view.embed (negRef vars)) (j.set view.key (start + k)) = some ⟨false⟩
  defined : ∀ k < count, ∀ j, Agrees active fixed j → ∀ t (r : Port vars t),
    (read (view.inner.embed (body.lift (portLeft r))) (j.set view.key (start + k))).isSome

variable {test : Expr P vars .bool} {stmt : Stmt P true vars vars}

theorem traceExit {Q : InstructionSet.{u,x} Data} {source : Interpretation.{u,x,y} Q}
    {state : List (Ty Data)} {test : Expr Q state .bool} {stmt : Stmt Q true state state}
    (pack : Tuple source.Value state → Tuple m.Value vars)
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (fixed : Index all.length)
    (testCorrect : ∀ {k store} {b : Bool}, AtIteration view fixed k (pack store) →
      test.eval source store = some ⟨b⟩ → ∀ j, Agrees active fixed j →
      read (view.inner.embed guard) (j.set view.key k) = some ⟨b⟩)
    (bodyCorrect : ∀ {k store updated}, AtIteration view fixed k (pack store) →
      Exec source stmt store (some updated) →
      RealizesOn read view.inner.embed next (pack updated) (view.key :: active) (fixed.set view.key k))
    {count : Nat} {store final : Tuple source.Value state}
    (trace : WhileTrace source test stmt count store final) (start : Nat)
    (entry : AtIteration view fixed start (pack store)) :
    Exits view fixed start count (pack final) := by
  induction trace generalizing start with
  | stop h =>
    refine ⟨entry, ?_, ?_, ?_⟩
    · intro j eq
      exact exitTest view negSem _ (testCorrect entry h j eq)
    · intro k lt
      omega
    · intro k lt
      omega
  | @step k store updated final h run tail ih =>
    have reached := ih (start + 1) (stepIteration view (bodyCorrect entry run))
    have offset (j : Nat) : start + (j + 1) = start + 1 + j := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [offset]
      exact reached.store
    · intro j eq
      rw [offset]
      exact reached.stop _ eq
    · intro i lt j eq
      cases i with
      | zero => exact exitTest view negSem _ (testCorrect entry h j eq)
      | succ i =>
        rw [offset]
        exact reached.prior i (by omega) j eq
    · intro i lt j eq t r
      cases i with
      | zero =>
        have atSlot := slotAt view entry (sampleAgrees view eq start) r
        change (read (view.inner.embed (body.lift (portLeft r))) (j.set view.key start)).isSome
        rw [atSlot]
        rfl
      | succ i =>
        rw [offset]
        exact reached.defined i (by omega) j eq t r

@[expose] def flags (j : Index all.length) (k : Nat) : Option Bool :=
  (read (view.embed (negRef vars)) (j.set view.key k)).map ULift.down

@[expose] def samples (j : Index all.length) (r : Port vars t) (k : Nat) : Option (m.Value t) :=
  read (view.inner.embed (body.lift (portLeft r))) (j.set view.key k)

theorem samples_zero (j : Index all.length) (r : Port vars t) :
    samples view j r 0 = read (view.embed ((Code.loop init body guard next neg).lift (init.get r)))
      (j.set view.key 0) :=
  thetaZero view r _ (by simp [Index.set])

theorem samples_succ (j : Index all.length) (r : Port vars t) (k : Nat) :
    samples view j r (k + 1) = read (view.inner.embed (next.get r)) (j.set view.key k) := by
  have setTwice : (j.set view.key (k + 1)).set view.key k = j.set view.key k := by
    funext l
    by_cases h : l = view.key <;> simp [Index.set, h]
  rw [samples, thetaNext view r _ k (by simp [Index.set]), setTwice]

theorem passEquation (j : Index all.length) :
    read (view.embed (passRef vars)) j = (firstTrue (flags view j)).map ULift.up := by
  refine (view.eqs j _ (passRef vars)).trans ?_
  change rowValue m env (loopRows body guard neg active.head? view.embed
    (body.rows view.inner.holes view.inner.embed (some view.key)) (passRef vars)) read j = _
  rw [loopRows_pass]
  rfl

theorem evalEquation (j : Index all.length) (r : Port vars t) :
    read (view.embed (portLeft r)) j =
      (read (view.embed (passRef vars)) j).elim none
        (fun count => monotonize (samples view j r) count.down) := by
  refine (view.eqs j _ (portLeft r)).trans ?_
  change rowValue m env (loopRows body guard neg active.head? view.embed
    (body.rows view.inner.holes view.inner.embed (some view.key)) (portLeft r)) read j = _
  rw [loopRows_exit]
  rfl

theorem passValue {fixed : Index all.length} {k : Nat} {final : Tuple m.Value vars}
    (exit : Exits view fixed 0 k final) (j : Index all.length) (agree : Agrees active fixed j) :
    read (view.embed (passRef vars)) j = some ⟨k⟩ := by
  have atExit : flags view j k = some true := by
    unfold flags
    have h := exit.stop j agree
    rw [Nat.zero_add] at h
    rw [h]
    rfl
  have before (i : Nat) (lt : i < k) : flags view j i = some false := by
    unfold flags
    have h := exit.prior i lt j agree
    rw [Nat.zero_add] at h
    rw [h]
    rfl
  rw [passEquation view j, (firstTrue_eq_some_iff_samples _ _).mpr ⟨atExit, before⟩]
  rfl

theorem evalValue {fixed : Index all.length} {k : Nat} {final : Tuple m.Value vars}
    (exit : Exits view fixed 0 k final) (j : Index all.length) (agree : Agrees active fixed j)
    {t : Ty Data} (r : Port vars t) :
    read (view.embed (portLeft r)) j = some (final.get r) := by
  rw [evalEquation view j r, passValue view exit j agree]
  apply (monotonize_eq_some_iff _ _ _).mpr
  constructor
  · have finalSample := slotAt view exit.store (sampleAgrees view agree (0 + k)) r
    simpa only [samples, Nat.zero_add] using finalSample
  · intro i lt
    simpa only [samples, Nat.zero_add] using exit.defined i lt j agree t r

theorem loopCorrect
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (fixed : Index all.length)
    (testCorrect : ∀ {k store} {b : Bool}, AtIteration view fixed k store →
      test.eval m store = some ⟨b⟩ → ∀ j, Agrees active fixed j →
      read (view.inner.embed guard) (j.set view.key k) = some ⟨b⟩)
    (bodyCorrect : ∀ {k store updated}, AtIteration view fixed k store →
      Exec m stmt store (some updated) →
      RealizesOn read view.inner.embed next updated (view.key :: active) (fixed.set view.key k))
    {store final : Tuple m.Value vars}
    (entry : RealizesOn read (fun r => view.embed ((Code.loop init body guard next neg).lift r))
      init store active fixed)
    (run : Exec m (.while rfl test stmt) store (some final)) :
    RealizesOn read view.embed ((ports vars).map fun _ r => portLeft r) final active fixed := by
  obtain ⟨k, trace⟩ := run.while_trace
  have exit := traceExit view id negSem fixed testCorrect bodyCorrect trace 0 (atEntry view entry)
  intro j agree t r
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact evalValue view exit j agree r

variable (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
variable (fixed : Index all.length)
variable (testCorrect : ∀ {k store} {b : Bool}, AtIteration view fixed k store →
  test.eval m store = some ⟨b⟩ → ∀ j, Agrees active fixed j →
  read (view.inner.embed guard) (j.set view.key k) = some ⟨b⟩)
variable (bodyCorrect : ∀ {k store updated}, AtIteration view fixed k store →
  Exec m stmt store (some updated) →
  RealizesOn read view.inner.embed next updated (view.key :: active) (fixed.set view.key k))
variable {Ready : Nat → Tuple m.Value vars → Prop}
variable (guardReady : ∀ {k store}, Ready k store → ∃ b : Bool, test.eval m store = some ⟨b⟩)
variable (stepReady : ∀ {k store}, Ready (k + 1) store → test.eval m store = some ⟨true⟩ →
  ∃ updated, Exec m stmt store (some updated) ∧ Ready k updated)

include negSem testCorrect in
private theorem guardOfFlag {j : Index all.length} (agree : Agrees active fixed j)
    {k : Nat} {store : Tuple m.Value vars} (entry : AtIteration view fixed k store)
    (defined : ∃ b : Bool, test.eval m store = some ⟨b⟩)
    {b : Bool} (flag : flags view j k = some (!b)) : test.eval m store = some ⟨b⟩ := by
  obtain ⟨actual, ran⟩ := defined
  unfold flags at flag
  rw [exitTest view negSem _ (testCorrect entry ran j agree)] at flag
  cases actual <;> cases b <;> simp_all

include negSem testCorrect bodyCorrect guardReady stepReady in
private theorem traceFromFlags {j : Index all.length} (agree : Agrees active fixed j)
    (start k : Nat) {store : Tuple m.Value vars} (entry : AtIteration view fixed start store)
    (ready : Ready k store)
    (stop : flags view j (start + k) = some true)
    (earlier : ∀ q < k, flags view j (start + q) = some false) :
    ∃ final, WhileTrace m test stmt k store final ∧ AtIteration view fixed (start + k) final := by
  induction k generalizing start store with
  | zero =>
    have test := guardOfFlag view negSem fixed testCorrect agree entry
      (guardReady ready) (b := false) stop
    exact ⟨store, .stop test, entry⟩
  | succ k ih =>
    have test := guardOfFlag view negSem fixed testCorrect agree entry
      (guardReady ready) (b := true) (earlier 0 (Nat.zero_lt_succ _))
    obtain ⟨next, ran, tailReady⟩ := stepReady ready test
    have offset (q : Nat) : start + 1 + q = start + (q + 1) := by omega
    obtain ⟨final, rest, last⟩ := ih (start + 1) (stepIteration view (bodyCorrect entry ran)) tailReady
      (by rw [offset]; exact stop)
      (fun q hq => by rw [offset]; exact earlier (q + 1) (by omega))
    exact ⟨final, .step test ran rest, by rw [← offset]; exact last⟩

include negSem testCorrect bodyCorrect guardReady stepReady in
/-- A defined selected eval gives a trace at the shared pass count. The
current loop can be inside fixed enclosing coordinates. -/
theorem loopTraceOfDefined {j : Index all.length} (agree : Agrees active fixed j)
    {store : Tuple m.Value vars}
    (entry : RealizesOn read (fun r => view.embed ((Code.loop init body guard next neg).lift r))
      init store active fixed)
    (ready : ∀ k, read (view.embed (passRef vars)) j = some ⟨k⟩ → Ready k store)
    {r : Port vars t} {value : m.Value t} (defined : read (view.embed (portLeft r)) j = some value) :
    ∃ k final, WhileTrace m test stmt k store final ∧ final.get r = value ∧
      read (view.embed (passRef vars)) j = some ⟨k⟩ ∧
      (∀ q < k, (samples view j r q).isSome) := by
  rw [evalEquation view j r, passEquation view j] at defined
  cases first : firstTrue (flags view j) with
  | none => rw [first] at defined; cases defined
  | some k =>
    rw [first] at defined
    obtain ⟨sample, prior⟩ := (monotonize_eq_some_iff _ _ _).mp defined
    obtain ⟨stop, earlier⟩ := (firstTrue_eq_some_iff_samples _ _).mp first
    have pass : read (view.embed (passRef vars)) j = some ⟨k⟩ := by
      rw [passEquation view j, first]
      rfl
    obtain ⟨final, trace, last⟩ :=
      traceFromFlags view negSem fixed testCorrect bodyCorrect (Ready := Ready) guardReady (@stepReady) agree 0 k
        (atEntry view entry) (ready k pass) (by simpa only [Nat.zero_add] using stop)
        (fun q hq => by simpa only [Nat.zero_add] using earlier q hq)
    have lastSample : samples view j r k = some (final.get r) := by
      simpa only [samples, Nat.zero_add] using slotAt view last (sampleAgrees view agree (0 + k)) r
    exact ⟨k, final, trace, Option.some.inj (lastSample.symm.trans sample), pass, prior⟩

end Silmaril.SSA.PEG.Simple.Structured.Proofs
