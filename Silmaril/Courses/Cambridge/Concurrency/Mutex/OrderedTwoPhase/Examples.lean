module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.OrderedTwoPhase
public import Mathlib.Data.String.Basic
import Silmaril.Courses.Cambridge.Concurrency.Mutex.Equivalence
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Permutation

/-! # Checked cases for Exercise 38 and the statement of Conjecture 28 -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex.OrderedTwoPhase.Examples

/-! ## Straight-line fixtures -/

def layout : Layout := ⟨Equiv.refl _, inferInstance⟩

inductive Instruction where
  | lock (name : MutexName)
  | unlock (name : MutexName)
  | write (loc : Loc) (value : Int)

def Instruction.expr : Instruction → Expr
  | .lock name => .lock name
  | .unlock name => .unlock name
  | .write loc n => .assign loc (.int n)

def Instruction.label : Instruction → Action
  | .lock name => .lock name
  | .unlock name => .unlock name
  | .write loc n => .write loc n

def script : List Instruction → Expr
  | [] => .skip
  | head :: tail => .seq head.expr (script tail)

def labels (instructions : List Instruction) : List Action :=
  instructions.flatMap fun instruction => [instruction.label, .tau]

/-- These fixtures have one outgoing transition at each nonterminal
expression. The certificate accounts for every possible local trace. -/
private inductive FixedTrace : Expr → List Action → Prop where
  | done : FixedTrace .skip []
  | step {e next : Expr} {action : Action} {rest : List Action}
      (step : ThreadStep e action next)
      (unique : ∀ {a e'}, ThreadStep e a e' → a = action ∧ e' = next)
      (tail : FixedTrace next rest) : FixedTrace e (action :: rest)

private theorem FixedTrace.inspect {e : Expr} {word : List Action}
    (fixed : FixedTrace e word) {trace : List Action} {after : Expr}
    (run : threadLTS.MTr e trace after) :
    trace <+: word ∧ (LocalTerminal after → trace = word) := by
  induction fixed generalizing trace after with
  | done =>
      cases run with
      | refl => exact ⟨List.nil_prefix, fun _ => rfl⟩
      | stepL first _ => cases first
  | step first unique _ ih =>
      cases run with
      | refl => exact ⟨List.nil_prefix, fun halted => False.elim (halted _ _ first)⟩
      | stepL step tail =>
          obtain ⟨rfl, rfl⟩ := unique step
          obtain ⟨isPrefix, complete⟩ := ih tail
          exact ⟨List.cons_prefix_cons.mpr ⟨rfl, isPrefix⟩,
            fun halted => congrArg (fun rest => _ :: rest) (complete halted)⟩

private theorem FixedTrace.reaches_terminal {e : Expr} {word : List Action}
    (fixed : FixedTrace e word) : ∃ after, threadLTS.MTr e word after ∧ LocalTerminal after := by
  induction fixed with
  | done => exact ⟨_, .refl, fun _ _ step => by cases step⟩
  | step step _ _ ih =>
      obtain ⟨after, run, halted⟩ := ih
      exact ⟨after, .stepL step run, halted⟩

private theorem Instruction.step (instruction : Instruction) :
    ThreadStep instruction.expr instruction.label .skip := by
  cases instruction with
  | lock name => exact .lock name
  | unlock name => exact .unlock name
  | write loc n => exact .assignValue loc n

private theorem Instruction.seq_unique (instruction : Instruction) (rest : Expr)
    {action : Action} {after : Expr} (step : ThreadStep (.seq instruction.expr rest) action after) :
    action = instruction.label ∧ after = .seq .skip rest := by
  cases instruction with
  | lock =>
      cases step with
      | seqStep inner =>
          cases inner
          exact ⟨rfl, rfl⟩
  | unlock =>
      cases step with
      | seqStep inner =>
          cases inner
          exact ⟨rfl, rfl⟩
  | write =>
      cases step with
      | seqStep inner =>
          cases inner with
          | assignValue => exact ⟨rfl, rfl⟩
          | assignStep smaller => cases smaller

private theorem script_fixed (instructions : List Instruction) :
    FixedTrace (script instructions) (labels instructions) := by
  induction instructions with
  | nil => exact FixedTrace.done
  | cons instruction tail ih =>
      refine FixedTrace.step (ThreadStep.seqStep instruction.step) (instruction.seq_unique _) ?_
      refine FixedTrace.step (ThreadStep.seqSkip _) ?_ ih
      intro _ _ step
      cases step with
      | seqSkip => exact ⟨rfl, rfl⟩
      | seqStep inner => cases inner

private theorem script_obeys {instructions : List Instruction}
    (conditions : PrefixConditions layout (labels instructions))
    (released : Released (labels instructions)) : Obeys layout (script instructions) := by
  intro trace after run
  obtain ⟨isPrefix, complete⟩ := (script_fixed instructions).inspect run
  exact ⟨conditions.prefix isPrefix, fun halted => by simpa only [complete halted] using released⟩

def checkedWrite : List Instruction := [.lock "l", .write "l" 1, .unlock "l"]

theorem checkedWrite_obeys : Obeys layout (script checkedWrite) := by
  apply script_obeys
  · constructor <;>
      simp [checkedWrite, labels, Instruction.label, layout, heldAfter, MutexState.initial,
        accessGuard, bracketGuard, phaseGuard, orderGuard]
  · intro name
    by_cases same : name = "l" <;>
      simp [checkedWrite, labels, Instruction.label, heldAfter, MutexState.initial, same]


private theorem lock_sequence_terminal {s : SharedState} {name : MutexName} {body : Expr}
    (held : s.mutexes name = true) : Terminal ⟨.seq (.lock name) body, s⟩ := by
  intro next step
  cases step with
  | seqStep inner => exact lock_terminal held _ inner

/-! ## The initial-store counterexample -/

def cellContext : TypeEnv := (∅ : TypeEnv).insert "l" .intref

theorem checkedWrite_typed : HasType cellContext (script checkedWrite) .unit :=
  .seq (.lock "l") (.seq (.assign (by simp [cellContext]) (.int 1)) (.seq (.unlock "l") .skip))

theorem empty_store_excludes_cell : ¬ L1.StoreCovers cellContext ∅ :=
  fun covers => Finmap.notMem_empty (covers "l" (by simp [cellContext]))

def missingCellBlocked : Config :=
  ⟨.parallel (script [.write "l" 1, .unlock "l"]) (script checkedWrite),
    (SharedState.mk ∅ MutexState.initial).setMutex "l" true⟩

theorem missingCell_reachable :
    Steps (start (parallel [script checkedWrite, script checkedWrite]) ∅) missingCellBlocked :=
  .head (.parallelLeft (.seqStep (.lock rfl))) (.single (.parallelLeft .seqSkip))

theorem missingCell_terminal : Terminal missingCellBlocked := by
  intro next step
  unfold missingCellBlocked at step
  cases step with
  | parallelLeft inner =>
      cases inner with
      | seqStep write =>
          cases write with
          | assignValue present => exact Finmap.notMem_empty present
          | assignStep smaller => cases smaller
  | parallelRight inner =>
      exact lock_sequence_terminal (by simp [SharedState.setMutex]) _ inner

/-- Exercise 39 for the literal store quantifier. Both threads obey the
discipline, but the absent cell keeps the first thread from releasing its
mutex. The second thread still proposes a lock at the terminal state. -/
theorem conjecture28_false : ¬ Conjecture28 := by
  intro conjecture
  have threads : ∀ e ∈ [script checkedWrite, script checkedWrite],
      HasType cellContext e .unit ∧ Obeys layout e := by
    intro e member
    have same : e = script checkedWrite := by simpa using member
    subst e
    exact ⟨checkedWrite_typed, checkedWrite_obeys⟩
  have free := (conjecture layout cellContext _ threads).2
  exact free ∅ trivial _ missingCell_reachable missingCell_terminal "l" _
    (.parallelRight (.seqStep (.lock "l")))

/-! ## Exercise 38 deadlocks -/

private theorem empty_covers : L1.StoreCovers (∅ : TypeEnv) (∅ : Store) := by
  intro _ present
  exact False.elim (Finmap.notMem_empty present)

def takesWithoutReleasing : List Instruction := [.lock "a"]

def takesAndReleases : List Instruction := [.lock "a", .unlock "a"]

theorem takesAndReleases_obeys : Obeys layout (script takesAndReleases) := by
  apply script_obeys
  · constructor <;>
      simp [takesAndReleases, labels, Instruction.label, layout, heldAfter, MutexState.initial,
        accessGuard, bracketGuard, phaseGuard, orderGuard]
  · intro name
    by_cases same : name = "a" <;>
      simp [takesAndReleases, labels, Instruction.label, heldAfter, MutexState.initial, same]

/-- This script meets every prefix condition, including the alternation of
lock events. Only the requirement at local termination fails. -/
theorem takesWithoutReleasing_prefixes {trace : List Action} {after : Expr}
    (run : threadLTS.MTr (script takesWithoutReleasing) trace after) :
    PrefixConditions layout trace := by
  have conditions : PrefixConditions layout (labels takesWithoutReleasing) := by
    constructor <;>
      simp [takesWithoutReleasing, labels, Instruction.label, layout, heldAfter, MutexState.initial,
        accessGuard, bracketGuard, phaseGuard, orderGuard]
  exact conditions.prefix ((script_fixed _).inspect run).1

theorem takesWithoutReleasing_violates_release :
    ∃ trace after, threadLTS.MTr (script takesWithoutReleasing) trace after ∧
      LocalTerminal after ∧ ¬ Released trace := by
  obtain ⟨after, run, halted⟩ := (script_fixed takesWithoutReleasing).reaches_terminal
  refine ⟨_, after, run, halted, fun released => ?_⟩
  have bit := released "a"
  simp [takesWithoutReleasing, labels, Instruction.label, heldAfter] at bit

def releaseBlocked (store : Store) : Config :=
  ⟨.parallel .skip (script takesAndReleases),
    (SharedState.mk store MutexState.initial).setMutex "a" true⟩

/-- Exercise 38, terminal-release premise. The other thread follows the full
discipline, and the example uses a covering store for the empty context. -/
theorem terminal_release_necessary :
    ¬ DeadlockFree (L1.StoreCovers ∅) [script takesWithoutReleasing, script takesAndReleases] := by
  intro free
  have reaches :
      Steps (start (parallel [script takesWithoutReleasing, script takesAndReleases]) ∅)
        (releaseBlocked ∅) :=
    .head (.parallelLeft (.seqStep (.lock rfl))) (.single (.parallelLeft .seqSkip))
  have halted : Terminal (releaseBlocked ∅) := by
    intro next step
    unfold releaseBlocked at step
    cases step with
    | parallelLeft inner => cases inner
    | parallelRight inner =>
        exact lock_sequence_terminal (by simp [SharedState.setMutex]) _ inner
  exact free ∅ empty_covers _ reaches halted "a" _ (.parallelRight (.seqStep (.lock "a")))

example : HasType ∅ (script takesWithoutReleasing) .unit := .seq (.lock "a") .skip

example : HasType ∅ (script takesAndReleases) .unit :=
  .seq (.lock "a") (.seq (.unlock "a") .skip)


private theorem a_before_b : ("a" : String) < "b" := by
  apply String.lt_iff_toList_lt.mpr
  change List.Lex (· < ·) ['a'] ['b']
  exact .rel (by decide)

private theorem b_before_c : ("b" : String) < "c" := by
  apply String.lt_iff_toList_lt.mpr
  change List.Lex (· < ·) ['b'] ['c']
  exact .rel (by decide)

def increasing : List Instruction :=
  [.lock "a", .lock "b", .unlock "b", .unlock "a"]

def decreasing : List Instruction :=
  [.lock "b", .lock "a", .unlock "b", .unlock "a"]

theorem increasing_obeys : Obeys layout (script increasing) := by
  apply script_obeys
  · constructor <;>
      simp [increasing, labels, Instruction.label, layout, heldAfter, MutexState.initial,
        accessGuard, bracketGuard, phaseGuard, orderGuard, a_before_b]
  · intro name
    by_cases isA : name = "a" <;> by_cases isB : name = "b" <;>
      simp [increasing, labels, Instruction.label, heldAfter, MutexState.initial, isA, isB]

theorem decreasing_other_clauses {trace : List Action} {after : Expr}
    (run : threadLTS.MTr (script decreasing) trace after) :
    EveryEvent (accessGuard layout) trace ∧ EveryEvent bracketGuard trace ∧
      EveryEvent phaseGuard trace ∧ (LocalTerminal after → Released trace) := by
  have access : EveryEvent (accessGuard layout) (labels decreasing) := by
    simp [decreasing, labels, Instruction.label, accessGuard]
  have bracketing : EveryEvent bracketGuard (labels decreasing) := by
    simp [decreasing, labels, Instruction.label, heldAfter, MutexState.initial, bracketGuard]
  have phase : EveryEvent phaseGuard (labels decreasing) := by
    simp [decreasing, labels, Instruction.label, phaseGuard]
  obtain ⟨isPrefix, complete⟩ := (script_fixed decreasing).inspect run
  refine ⟨access.prefix isPrefix, bracketing.prefix isPrefix, phase.prefix isPrefix, ?_⟩
  intro halted name
  rw [complete halted]
  by_cases isA : name = "a" <;> by_cases isB : name = "b" <;>
    simp [decreasing, labels, Instruction.label, heldAfter, MutexState.initial, isA, isB]

theorem decreasing_violates_order :
    ∃ trace after, threadLTS.MTr (script decreasing) trace after ∧
      ¬ EveryEvent (orderGuard layout) trace := by
  obtain ⟨after, run, _⟩ := (script_fixed decreasing).reaches_terminal
  refine ⟨_, after, run, fun ordered => ?_⟩
  have cannot : ¬ layout.order.lt "b" "a" := by
    exact not_lt_of_ge (le_of_lt a_before_b)
  have rule := ordered [.lock "b", .tau] (.lock "a")
    [.tau, .unlock "b", .tau, .unlock "a", .tau] rfl
  exact cannot (rule (.lock "b") (by simp))

def orderBlocked (store : Store) : Config :=
  ⟨.parallel (script [.lock "b", .unlock "b", .unlock "a"])
      (script [.lock "a", .unlock "b", .unlock "a"]),
    ((SharedState.mk store MutexState.initial).setMutex "a" true).setMutex "b" true⟩

/-- Exercise 38, acquisition order. Both threads acquire one mutex and
then wait for the other. The initial store covers the empty context. -/
theorem increasing_order_necessary :
    ¬ DeadlockFree (L1.StoreCovers ∅) [script increasing, script decreasing] := by
  intro free
  have different : ("b" : MutexName) ≠ "a" := by decide
  have available :
      ((SharedState.mk ∅ MutexState.initial).setMutex "a" true).mutexes "b" = false := by
    simp [SharedState.setMutex, different, MutexState.initial]
  have reaches : Steps (start (parallel [script increasing, script decreasing]) ∅)
      (orderBlocked ∅) :=
    .head (.parallelLeft (.seqStep (.lock rfl)))
      (.head (.parallelLeft .seqSkip)
        (.head (.parallelRight (.seqStep (.lock available)))
          (.single (.parallelRight .seqSkip))))
  have heldA : (orderBlocked ∅).shared.mutexes "a" = true := by
    have different : ("a" : MutexName) ≠ "b" := by decide
    simp [orderBlocked, SharedState.setMutex, different]
  have halted : Terminal (orderBlocked ∅) := by
    intro next step
    unfold orderBlocked at step
    cases step with
    | parallelLeft inner =>
        exact lock_sequence_terminal (by simp [SharedState.setMutex]) _ inner
    | parallelRight inner => exact lock_sequence_terminal heldA _ inner
  exact free ∅ empty_covers _ reaches halted "a" _ (.parallelRight (.seqStep (.lock "a")))

example : HasType ∅ (script increasing) .unit :=
  .seq (.lock "a") (.seq (.lock "b") (.seq (.unlock "b") (.seq (.unlock "a") .skip)))

example : HasType ∅ (script decreasing) .unit :=
  .seq (.lock "b") (.seq (.lock "a") (.seq (.unlock "b") (.seq (.unlock "a") .skip)))


/-! ## Exercise 38 serializability

The fixed local scripts allow every serial prefix to be checked, as required
on p. 97.
-/

private theorem FixedTrace.seq {left right : Expr} {leftWord rightWord : List Action}
    (first : FixedTrace left leftWord) (second : FixedTrace right rightWord) :
    FixedTrace (.seq left right) (leftWord ++ .tau :: rightWord) := by
  induction first with
  | done =>
      refine .step (.seqSkip _) ?_ second
      intro _ _ step
      cases step with
      | seqSkip => exact ⟨rfl, rfl⟩
      | seqStep inner => cases inner
  | step head unique _ ih =>
      refine .step (.seqStep head) ?_ ih
      intro _ _ step
      cases step with
      | seqSkip => cases head
      | seqStep inner =>
          obtain ⟨rfl, rfl⟩ := unique inner
          exact ⟨rfl, rfl⟩

private def traceWrite (store : Store) : Action → Store
  | .write loc n => store.insert loc n
  | _ => store

private theorem effect_store {action : Action} {s s' : SharedState}
    (effect : Effect action s s') : traceWrite s.store action = s'.store := by
  cases effect <;> rfl

private theorem store_trace {before after : Config} (run : Steps before after) :
    ∃ word, threadLTS.MTr before.expr word after.expr ∧
      word.foldl traceWrite before.shared.store = after.shared.store := by
  induction run with
  | refl => exact ⟨[], .refl, rfl⟩
  | tail _ step ih =>
      obtain ⟨word, trace, store⟩ := ih
      obtain ⟨action, localStep, effect⟩ := step.toLabelledStep
      refine ⟨word ++ [action], Cslib.LTS.MTr.stepR threadLTS trace localStep, ?_⟩
      rw [List.foldl_append, store]
      exact effect_store effect

private def observe (store : Store) : Option Int × Option Int × Option Int :=
  (L1.Store.lookup store "a", L1.Store.lookup store "b", L1.Store.lookup store "c")

private def observedPrefixes (store : Store) (word : List Action) :
    List (Option Int × Option Int × Option Int) :=
  word.inits.map (fun history => observe (history.foldl traceWrite store))

private theorem observation_of_serial_prefix {left right : List Instruction} {s : Store}
    {after : Config} (run : Steps (start (.seq (script left) (script right)) s) after) :
    observe after.shared.store ∈ observedPrefixes s (labels left ++ .tau :: labels right) := by
  obtain ⟨word, trace, store⟩ := store_trace run
  have history := ((script_fixed left).seq (script_fixed right)).inspect trace
  exact List.mem_map.mpr ⟨word, (List.mem_inits _ _).mpr history.1, congrArg observe store⟩

def cellStore : Store := (((∅ : Store).insert "a" 0).insert "b" 0).insert "c" 0

def cellTypes : TypeEnv :=
  (((∅ : TypeEnv).insert "a" .intref).insert "b" .intref).insert "c" .intref

private theorem cellStore_covers : L1.StoreCovers cellTypes cellStore := by
  intro loc present
  simpa [cellTypes, cellStore, Finmap.notMem_empty] using present

private theorem two_scripts_not_serializable {left right : List Instruction} {after : Config}
    (run : Steps (start (parallel [script left, script right]) cellStore) after)
    (halted : Terminal after)
    (leftFirst : observe after.shared.store ∉ observedPrefixes cellStore (labels left ++ .tau :: labels right))
    (rightFirst : observe after.shared.store ∉ observedPrefixes cellStore (labels right ++ .tau :: labels left)) :
    ¬ Serializable (L1.StoreCovers cellTypes) [script left, script right] := by
  intro serializable
  obtain ⟨order, perm, e, serial⟩ := serializable cellStore cellStore_covers after run halted
  rcases List.perm_pair.mp perm with rfl | rfl
  · exact leftFirst (observation_of_serial_prefix (after := ⟨e, after.shared⟩) serial)
  · exact rightFirst (observation_of_serial_prefix (after := ⟨e, after.shared⟩) serial)

private theorem parallelLeft_steps {before after : Config} (run : Steps before after) (right : Expr) :
    Steps ⟨.parallel before.expr right, before.shared⟩
      ⟨.parallel after.expr right, after.shared⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.parallelLeft step)

private theorem parallelRight_steps {before after : Config} (run : Steps before after) (left : Expr) :
    Steps ⟨.parallel left before.expr, before.shared⟩
      ⟨.parallel left after.expr, after.shared⟩ := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.parallelRight step)

private theorem both_completed {s : SharedState} : Terminal ⟨.parallel .skip .skip, s⟩ := by
  intro next step
  cases step with
  | parallelLeft inner => cases inner
  | parallelRight inner => cases inner

private theorem run_write {s : SharedState} {rest : List Instruction}
    (loc : Loc) (n : Int) (present : loc ∈ s.store) :
    Steps ⟨script (.write loc n :: rest), s⟩ ⟨script rest, s.write loc n⟩ :=
  .head (.seqStep (.assignValue present)) (.single .seqSkip)


def unprotectedLeft : List Instruction := [.write "a" 1, .write "b" 1]

def unprotectedRight : List Instruction := [.write "b" 2, .write "a" 2]

theorem unprotected_other_clauses {instructions : List Instruction} {trace : List Action} {after : Expr}
    (which : instructions = unprotectedLeft ∨ instructions = unprotectedRight)
    (run : threadLTS.MTr (script instructions) trace after) :
    EveryEvent bracketGuard trace ∧ EveryEvent phaseGuard trace ∧ EveryEvent (orderGuard layout) trace ∧
      (LocalTerminal after → Released trace) := by
  obtain ⟨isPrefix, complete⟩ := (script_fixed instructions).inspect run
  have checks : EveryEvent bracketGuard (labels instructions) ∧
      EveryEvent phaseGuard (labels instructions) ∧ EveryEvent (orderGuard layout) (labels instructions) ∧
      Released (labels instructions) := by
    rcases which with rfl | rfl <;>
      simp [unprotectedLeft, unprotectedRight, labels, Instruction.label, bracketGuard, phaseGuard,
        orderGuard, Released, heldAfter, MutexState.initial]
  exact ⟨checks.1.prefix isPrefix, checks.2.1.prefix isPrefix, checks.2.2.1.prefix isPrefix,
    fun halted => by simpa only [complete halted] using checks.2.2.2⟩

theorem unprotected_violates_access :
    ∃ trace after, threadLTS.MTr (script unprotectedLeft) trace after ∧
      ¬ EveryEvent (accessGuard layout) trace := by
  obtain ⟨after, run, _⟩ := (script_fixed unprotectedLeft).reaches_terminal
  exact ⟨_, after, run, fun checks =>
    Bool.false_ne_true (checks [] (.write "a" 1) [.tau, .write "b" 1, .tau] rfl)⟩

/-- Exercise 38, protection. The two threads write the cells in opposite
orders. Their mixed outcome is absent from both serial prefix lists. -/
theorem protection_necessary :
    ¬ Serializable (L1.StoreCovers cellTypes) [script unprotectedLeft, script unprotectedRight] := by
  let s : SharedState := ⟨cellStore, MutexState.initial⟩
  let s1 := s.write "a" 1
  let s2 := s1.write "b" 2
  let s3 := s2.write "a" 2
  let s4 := s3.write "b" 1
  apply two_scripts_not_serializable (after := ⟨.parallel .skip .skip, s4⟩)
  · refine (parallelLeft_steps (run_write (s := s) (rest := [.write "b" 1]) "a" 1
      (by simp [s, cellStore])) (script unprotectedRight)).trans ?_
    refine (parallelRight_steps (run_write (s := s1) (rest := [.write "a" 2]) "b" 2
      (by simp [s1, s, cellStore, SharedState.write])) (script [.write "b" 1])).trans ?_
    refine (parallelRight_steps (run_write (s := s2) (rest := []) "a" 2
      (by simp [s2, s1, s, cellStore, SharedState.write])) (script [.write "b" 1])).trans ?_
    exact parallelLeft_steps (run_write (s := s3) (rest := []) "b" 1
      (by simp [s3, s2, s1, s, cellStore, SharedState.write])) .skip
  · exact both_completed
  all_goals
    simp [s4, s3, s2, s1, s, SharedState.write, observe, observedPrefixes,
      unprotectedLeft, unprotectedRight, labels, Instruction.label, traceWrite, cellStore]


def guardedWrite (loc : Loc) (n : Int) : List Instruction :=
  [.lock loc, .write loc n, .unlock loc]

def releasesBetweenCells (n : Int) : List Instruction :=
  guardedWrite "a" n ++ guardedWrite "b" n ++ guardedWrite "c" n

theorem releasesBetweenCells_other_clauses (n : Int) {trace : List Action} {after : Expr}
    (run : threadLTS.MTr (script (releasesBetweenCells n)) trace after) :
    EveryEvent (accessGuard layout) trace ∧ EveryEvent bracketGuard trace ∧
      EveryEvent (orderGuard layout) trace ∧ (LocalTerminal after → Released trace) := by
  let full := labels (releasesBetweenCells n)
  have access : EveryEvent (accessGuard layout) full := by
    simp [full, releasesBetweenCells, guardedWrite, labels, Instruction.label, layout,
      heldAfter, accessGuard]
  have bracketing : EveryEvent bracketGuard full := by
    simp [full, releasesBetweenCells, guardedWrite, labels, Instruction.label,
      heldAfter, MutexState.initial, bracketGuard]
  have ordering : EveryEvent (orderGuard layout) full := by
    have a_before_c := lt_trans a_before_b b_before_c
    simp [full, releasesBetweenCells, guardedWrite, labels, Instruction.label, layout,
      orderGuard, a_before_b, a_before_c, b_before_c]
  obtain ⟨isPrefix, complete⟩ := (script_fixed _).inspect run
  refine ⟨access.prefix isPrefix, bracketing.prefix isPrefix, ordering.prefix isPrefix, ?_⟩
  intro halted name
  rw [complete halted]
  by_cases isA : name = "a" <;> by_cases isB : name = "b" <;> by_cases isC : name = "c" <;>
    simp [releasesBetweenCells, guardedWrite, labels, Instruction.label, heldAfter,
      MutexState.initial, isA, isB, isC]

theorem releasesBetweenCells_violates_phase (n : Int) :
    ∃ trace after, threadLTS.MTr (script (releasesBetweenCells n)) trace after ∧
      ¬ EveryEvent phaseGuard trace := by
  obtain ⟨after, run, _⟩ := (script_fixed (releasesBetweenCells n)).reaches_terminal
  refine ⟨_, after, run, fun phased => ?_⟩
  have premature := phased (labels (guardedWrite "a" n)) (.lock "b")
    (.tau :: labels ([.write "b" n, .unlock "b"] ++ guardedWrite "c" n)) rfl
  exact premature (.unlock "a") (by simp [guardedWrite, labels, Instruction.label])

private theorem run_guarded_write {s : SharedState} {rest : List Instruction}
    (loc : Loc) (n : Int) (present : loc ∈ s.store) (available : s.mutexes loc = false) :
    Steps ⟨script (guardedWrite loc n ++ rest), s⟩ ⟨script rest, s.write loc n⟩ := by
  have restored : (s.mutexes.set loc true).set loc false = s.mutexes := by
    simp only [MutexState.set, Function.update_idem, ← available, Function.update_eq_self]
  have same : ((s.setMutex loc true).write loc n).setMutex loc false = s.write loc n :=
    congrArg (SharedState.mk (s.write loc n).store) restored
  have unlocked : Step ⟨.unlock loc, (s.setMutex loc true).write loc n⟩ ⟨.skip, s.write loc n⟩ := by
    simpa only [same] using Step.unlock loc ((s.setMutex loc true).write loc n)
  exact .head (.seqStep (.lock available))
    (.head .seqSkip (.head (.seqStep (.assignValue present))
      (.head .seqSkip (.head (.seqStep unlocked) (.single .seqSkip)))))

/-- Exercise 38, two phases. Both scripts take the locks in increasing order
and release after each protected write. The parallel execution reaches
`(2, 1, 2)`, which neither serial ordering can match at any prefix. -/
theorem two_phase_necessary :
    ¬ Serializable (L1.StoreCovers cellTypes)
      [script (releasesBetweenCells 1), script (releasesBetweenCells 2)] := by
  let s : SharedState := ⟨cellStore, MutexState.initial⟩
  let s1 := s.write "a" 1
  let s2 := s1.write "a" 2
  let s3 := s2.write "b" 2
  let s4 := s3.write "b" 1
  let s5 := s4.write "c" 1
  let s6 := s5.write "c" 2
  apply two_scripts_not_serializable (after := ⟨.parallel .skip .skip, s6⟩)
  · let leftTail := guardedWrite "b" 1 ++ guardedWrite "c" 1
    let rightTail := guardedWrite "b" 2 ++ guardedWrite "c" 2
    refine (parallelLeft_steps (run_guarded_write (s := s) (rest := leftTail) "a" 1
      (by simp [s, cellStore]) rfl) (script (releasesBetweenCells 2))).trans ?_
    refine (parallelRight_steps (run_guarded_write (s := s1) (rest := rightTail) "a" 2
      (by simp [s1, s, cellStore, SharedState.write]) rfl) (script leftTail)).trans ?_
    refine (parallelRight_steps (run_guarded_write (s := s2) (rest := guardedWrite "c" 2) "b" 2
      (by simp [s2, s1, s, cellStore, SharedState.write]) rfl) (script leftTail)).trans ?_
    refine (parallelLeft_steps (run_guarded_write (s := s3) (rest := guardedWrite "c" 1) "b" 1
      (by simp [s3, s2, s1, s, cellStore, SharedState.write]) rfl) (script (guardedWrite "c" 2))).trans ?_
    refine (parallelLeft_steps (run_guarded_write (s := s4) (rest := []) "c" 1
      (by simp [s4, s3, s2, s1, s, cellStore, SharedState.write]) rfl) (script (guardedWrite "c" 2))).trans ?_
    exact parallelRight_steps (run_guarded_write (s := s5) (rest := []) "c" 2
      (by simp [s5, s4, s3, s2, s1, s, cellStore, SharedState.write]) rfl) .skip
  · exact both_completed
  all_goals
    simp [s6, s5, s4, s3, s2, s1, s, SharedState.write, observe, observedPrefixes,
      releasesBetweenCells, guardedWrite, labels, Instruction.label, traceWrite, cellStore]

private theorem script_typed {Γ : TypeEnv} (instructions : List Instruction)
    (declared : ∀ loc n, Instruction.write loc n ∈ instructions → loc ∈ Γ) :
    HasType Γ (script instructions) .unit := by
  induction instructions with
  | nil => exact .skip
  | cons instruction rest ih =>
      apply HasType.seq _ (ih (fun loc n member => declared loc n (List.mem_cons_of_mem _ member)))
      cases instruction with
      | lock name => exact .lock name
      | unlock name => exact .unlock name
      | write loc n => exact .assign (declared loc n (by simp)) (.int n)

example : HasType cellTypes (script unprotectedLeft) .unit := by
  apply script_typed
  intro loc n member
  simp [unprotectedLeft] at member
  rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [cellTypes]

example : HasType cellTypes (script unprotectedRight) .unit := by
  apply script_typed
  intro loc n member
  simp [unprotectedRight] at member
  rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [cellTypes]

example (n : Int) : HasType cellTypes (script (releasesBetweenCells n)) .unit := by
  apply script_typed
  intro loc value member
  simp [releasesBetweenCells, guardedWrite] at member
  rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [cellTypes]

end Silmaril.Courses.Cambridge.Concurrency.Mutex.OrderedTwoPhase.Examples
