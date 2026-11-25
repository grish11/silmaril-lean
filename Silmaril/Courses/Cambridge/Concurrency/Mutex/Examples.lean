module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.Equivalence
public import Silmaril.Courses.Cambridge.Concurrency.Mutex.Preservation

/-! # Mutex and labelled derivations from Cambridge chapter 7 -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex.Examples

theorem unlock_available {s : SharedState} {name : MutexName} (available : s.mutexes name = false) :
    Step ⟨.unlock name, s⟩ ⟨.skip, s⟩ := by
  have unchanged : s.setMutex name false = s := by
    rw [← available]
    cases s
    simp only [SharedState.setMutex, MutexState.set, Function.update_eq_self]
  simpa only [unchanged] using Step.unlock name s

/-- Expression-side lock transitions are possible independently of the state. -/
theorem held_lock_waits {s : SharedState} {name : MutexName} (held : s.mutexes name = true) :
    ThreadStep (.lock name) (.lock name) .skip ∧ Terminal ⟨.lock name, s⟩ :=
  ⟨.lock name, lock_terminal held⟩

theorem absent_read_cannot_apply {s : SharedState} {loc : Loc} (missing : loc ∉ s.store)
    (n : Int) : ThreadStep (.deref loc) (.read loc n) (.int n) ∧ ∀ s', ¬ Effect (.read loc n) s s' := by
  refine ⟨.deref loc n, ?_⟩
  intro s' effect
  cases effect with
  | read present => exact missing (Finmap.mem_of_lookup_eq_some present)

def guardedIncrement : Expr :=
  .seq (.lock "m") (.seq (.assign "l" (.binary (.int 1) .add (.deref "l"))) (.unlock "m"))

/-- The seven thread-local transitions on p. 95, for any proposed read value. -/
theorem guardedIncrement_labels (n : Int) :
    threadLTS.MTr guardedIncrement
      [.lock "m", .tau, .read "l" n, .tau, .write "l" (1 + n), .tau, .unlock "m"] .skip :=
  .stepL (ThreadStep.seqStep (ThreadStep.lock "m"))
    (.stepL (ThreadStep.seqSkip _)
      (.stepL (ThreadStep.seqStep (ThreadStep.assignStep
        (ThreadStep.binaryRight (.int 1) (ThreadStep.deref "l" n))))
        (.stepL (ThreadStep.seqStep (ThreadStep.assignStep (ThreadStep.add 1 n)))
          (.stepL (ThreadStep.seqStep (ThreadStep.assignValue "l" (1 + n)))
            (.stepL (ThreadStep.seqSkip _) (.stepL (ThreadStep.unlock "m") .refl))))))

def waitThenCopy (name : MutexName) (destination source : Loc) : Expr :=
  .seq (.lock name)
    (.seq (.assign destination (.deref source)) (.seq (.unlock "m1") (.unlock "m2")))

def exchangeStart (store : Store) : Config :=
  ⟨.parallel (.seq (.lock "m1") (waitThenCopy "m2" "l1" "l2"))
      (.seq (.lock "m2") (waitThenCopy "m1" "l2" "l1")), ⟨store, MutexState.initial⟩⟩

def deadlocked (store : Store) : Config :=
  ⟨.parallel (waitThenCopy "m2" "l1" "l2") (waitThenCopy "m1" "l2" "l1"),
    ((SharedState.mk store MutexState.initial).setMutex "m1" true).setMutex "m2" true⟩

/-- The two threads on p. 93 can each acquire their first lock. -/
theorem exchange_deadlocks (store : Store) : Steps (exchangeStart store) (deadlocked store) := by
  have different : ("m2" : MutexName) ≠ "m1" := by decide
  have secondAvailable :
      ((SharedState.mk store MutexState.initial).setMutex "m1" true).mutexes "m2" = false := by
    simp [SharedState.setMutex, different, MutexState.initial]
  exact .head (.parallelLeft (.seqStep (.lock rfl)))
    (.head (.parallelLeft .seqSkip)
      (.head (.parallelRight (.seqStep (.lock secondAvailable)))
        (.single (.parallelRight .seqSkip))))

private theorem wait_terminal {s : SharedState} {name : MutexName} {destination source : Loc}
    (held : s.mutexes name = true) : Terminal ⟨waitThenCopy name destination source, s⟩ := by
  intro next step
  unfold waitThenCopy at step
  cases step with
  | seqStep inner => exact lock_terminal held _ inner

theorem deadlocked_terminal (store : Store) : Terminal (deadlocked store) := by
  have different : ("m1" : MutexName) ≠ "m2" := by decide
  have held1 : (deadlocked store).shared.mutexes "m1" = true := by
    simp [deadlocked, SharedState.setMutex, different]
  have held2 : (deadlocked store).shared.mutexes "m2" = true := by
    simp [deadlocked, SharedState.setMutex]
  intro next step
  unfold deadlocked at step
  cases step with
  | parallelLeft inner => exact wait_terminal held2 _ inner
  | parallelRight inner => exact wait_terminal held1 _ inner

theorem deadlocked_typed {Γ : TypeEnv} (store : Store) (l1 : "l1" ∈ Γ) (l2 : "l2" ∈ Γ) :
    HasType Γ (deadlocked store).expr .proc :=
  .parallel
    (.thread (.seq (.lock "m2") (.seq (.assign l1 (.deref l2)) (.seq (.unlock "m1") (.unlock "m2")))))
    (.thread (.seq (.lock "m1") (.seq (.assign l2 (.deref l1)) (.seq (.unlock "m1") (.unlock "m2")))))

end Silmaril.Courses.Cambridge.Concurrency.Mutex.Examples
