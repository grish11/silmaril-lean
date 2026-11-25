module

public import Silmaril.Courses.Cambridge.Concurrency.Mutex.Global

/-! # Exercise 37

The C&DS 2025–26 concurrency slides (`cambridge2025concurrent`) give a read-and-set loop and a clear
operation (lecture 1, slide 33, repeated in lecture 3, slide 5). Lecture 4,
slide 23 also describes blocking acquisition and the result of `trylock`.
The bit model records successful acquisitions and failures of a held lock.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex.Comparison

inductive Operation where
  | acquire
  | release
  | retry
  | tryAcquire (success : Bool)

/-- One operation on the lock bit. The two attempt results are exposed
separately from successful acquisition. -/
inductive BitStep : Bool → Operation → Bool → Prop where
  | acquire : BitStep false .acquire true
  | release (held : Bool) : BitStep held .release false
  | retry : BitStep true .retry true
  | tryAvailable : BitStep false (.tryAcquire true) true
  | tryHeld : BitStep true (.tryAcquire false) true

/-- The successful acquisition of the C&DS bit model is exactly the
projection of an SPL `lock` step onto the named mutex. -/
theorem acquire_iff {s : SharedState} {name : MutexName} {heldAfter : Bool} :
    BitStep (s.mutexes name) .acquire heldAfter ↔
      ∃ after, Step ⟨.lock name, s⟩ ⟨.skip, after⟩ ∧ after.mutexes name = heldAfter := by
  constructor
  · intro bit
    generalize current : s.mutexes name = held at bit
    cases bit
    exact ⟨s.setMutex name true, .lock current, by simp [SharedState.setMutex]⟩
  · rintro ⟨_, step, bit⟩
    cases step with
    | lock available =>
        rw [available, ← bit]
        simpa [SharedState.setMutex] using BitStep.acquire

/-- Clearing the bit projects the SPL `unlock` step for either prior bit. -/
theorem release_iff {s : SharedState} {name : MutexName} {heldAfter : Bool} :
    BitStep (s.mutexes name) .release heldAfter ↔
      ∃ after, Step ⟨.unlock name, s⟩ ⟨.skip, after⟩ ∧ after.mutexes name = heldAfter := by
  constructor
  · intro bit
    generalize s.mutexes name = held at bit
    cases bit
    exact ⟨s.setMutex name false, .unlock name s, by simp [SharedState.setMutex]⟩
  · rintro ⟨_, step, bit⟩
    cases step
    rw [← bit]
    simpa [SharedState.setMutex] using BitStep.release (s.mutexes name)

/-- A held lock permits a failed spin iteration and a failed nonblocking
attempt in the comparison model. The SPL configuration has to wait. -/
theorem held_attempts {s : SharedState} {name : MutexName} (held : s.mutexes name = true) :
    BitStep true .retry true ∧ BitStep true (.tryAcquire false) true ∧
      Terminal ⟨.lock name, s⟩ :=
  ⟨.retry, .tryHeld, lock_terminal held⟩

end Silmaril.Courses.Cambridge.Concurrency.Mutex.Comparison
