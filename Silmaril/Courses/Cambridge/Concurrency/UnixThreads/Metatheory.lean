module

public import Silmaril.Courses.Cambridge.Concurrency.UnixThreads.Semantics
public import Silmaril.Courses.Cambridge.L1.Metatheory.Preservation

/-! # Invariants of the Unix-style thread exercise -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.UnixThreads

def PoolTyped (Γ : L1.TypeEnv) (pool : ThreadPool) : Prop :=
  ∀ {id command}, pool.lookup id = some command → HasType Γ command

private theorem PoolTyped.insert {Γ : L1.TypeEnv} {pool : ThreadPool} {id : ThreadId}
    {command : Command} (typed : PoolTyped Γ pool) (added : HasType Γ command) :
    PoolTyped Γ (pool.insert id command) := by
  intro other code lookup
  by_cases same : other = id
  · subst other
    rw [Finmap.lookup_insert] at lookup
    cases lookup
    exact added
  · rw [Finmap.lookup_insert_of_ne _ same] at lookup
    exact typed lookup

private theorem PoolTyped.erase {Γ : L1.TypeEnv} {pool : ThreadPool}
    (typed : PoolTyped Γ pool) (id : ThreadId) : PoolTyped Γ (pool.erase id) := by
  intro other code lookup
  by_cases same : other = id
  · subst other
    rw [Finmap.lookup_erase] at lookup
    contradiction
  · rw [Finmap.lookup_erase_ne same] at lookup
    exact typed lookup

/-- The scheduled actor exists in the source pool. -/
theorem Step.actor_mem {before after : Config} {id : ThreadId} (step : Step before id after) :
    id ∈ before.threads := by
  cases step <;> apply Finmap.mem_of_lookup_eq_some <;> assumption

theorem Step.preserves_typing {Γ : L1.TypeEnv} {before after : Config} {id : ThreadId}
    (step : Step before id after) (typed : PoolTyped Γ before.threads) :
    PoolTyped Γ after.threads := by
  cases step with
  | runStep thread inner =>
      cases typed thread with
      | run body next => exact typed.insert (.run (inner.preserves_type body) next)
  | runDone thread =>
      cases typed thread with
      | run _ next => exact typed.insert next
  | fork thread _ _ =>
      cases typed thread with
      | fork _ child next => exact PoolTyped.insert (typed.insert next) child
  | join thread _ _ =>
      cases typed thread with
      | join _ next => exact PoolTyped.insert (typed.erase _) next
  | send thread _ =>
      cases typed thread with
      | send _ next => exact typed.insert next
  | receive thread _ _ =>
      cases typed thread with
      | receive _ next => exact typed.insert next

private theorem store_insert_domain {s : L1.Store} {destination : L1.Loc}
    (allocated : destination ∈ s) (loc : L1.Loc) (value : Int) :
    loc ∈ s ↔ loc ∈ s.insert destination value := by
  rw [Finmap.mem_insert]
  exact ⟨Or.inr, fun h => h.elim (fun eq => eq ▸ allocated) id⟩

theorem Step.store_domain {before after : Config} {id : ThreadId} (step : Step before id after)
    (loc : L1.Loc) : loc ∈ before.store ↔ loc ∈ after.store := by
  cases step with
  | runStep _ inner => exact inner.store_domain loc
  | fork _ allocated _ => exact store_insert_domain allocated loc _
  | receive _ allocated _ => exact store_insert_domain allocated loc _
  | runDone | join | send => rfl

def PoolBounded (pool : ThreadPool) (nextId : ThreadId) : Prop :=
  ∀ {id}, id ∈ pool → id < nextId

private theorem PoolBounded.insert {pool : ThreadPool} {id nextId : ThreadId}
    {command : Command} (bound : PoolBounded pool nextId) (added : id < nextId) :
    PoolBounded (pool.insert id command) nextId := by
  intro other member
  rcases Finmap.mem_insert.mp member with rfl | old
  · exact added
  · exact bound old

private theorem PoolBounded.erase {pool : ThreadPool} {nextId : ThreadId}
    (bound : PoolBounded pool nextId) (id : ThreadId) :
    PoolBounded (pool.erase id) nextId :=
  fun member => bound (Finmap.mem_erase.mp member).2

theorem Step.preserves_id_bound {before after : Config} {id : ThreadId}
    (step : Step before id after) (bound : PoolBounded before.threads before.nextId) :
    PoolBounded after.threads after.nextId := by
  intro other member
  have actor := bound step.actor_mem
  cases step with
  | runStep | runDone | send | receive => exact (bound.insert actor) member
  | join => exact (PoolBounded.insert (bound.erase _) actor) member
  | fork =>
      have oldBound : PoolBounded before.threads (before.nextId + 1) :=
        fun h => Nat.lt_succ_of_lt (bound h)
      exact (PoolBounded.insert (oldBound.insert (Nat.lt_succ_of_lt actor))
        (Nat.lt_succ_self _)) member

theorem Step.nextId_le {before after : Config} {id : ThreadId} (step : Step before id after) :
    before.nextId ≤ after.nextId := by
  cases step with
  | fork => exact Nat.le_succ _
  | runStep | runDone | join | send | receive => exact Nat.le_refl _

def Config.WellFormed (Γ : L1.TypeEnv) (c : Config) : Prop :=
  PoolTyped Γ c.threads ∧ L1.StoreCovers Γ c.store ∧ PoolBounded c.threads c.nextId

theorem Config.start_wellFormed {Γ : L1.TypeEnv} {main : Command} {s : L1.Store}
    (typed : HasType Γ main) (covers : L1.StoreCovers Γ s) :
    (start main s).WellFormed Γ := by
  refine ⟨PoolTyped.insert ?_ typed, covers, PoolBounded.insert ?_ Nat.zero_lt_one⟩
  · intro id code lookup
    rw [Finmap.lookup_empty] at lookup
    contradiction
  · intro id member
    exact False.elim (Finmap.notMem_empty member)

theorem Step.preserves_wellFormed {Γ : L1.TypeEnv} {before after : Config} {id : ThreadId}
    (step : Step before id after) (valid : before.WellFormed Γ) :
    after.WellFormed Γ :=
  ⟨step.preserves_typing valid.1, fun loc present => (step.store_domain loc).mp (valid.2.1 loc present),
    step.preserves_id_bound valid.2.2⟩

theorem trace_preserves_wellFormed {Γ : L1.TypeEnv} {before after : Config}
    {schedule : List ThreadId} (trace : lts.MTr before schedule after) (valid : before.WellFormed Γ) :
    after.WellFormed Γ := by
  induction trace with
  | refl => exact valid
  | stepL step _ ih => exact ih (Step.preserves_wellFormed step valid)

theorem receive_waits {c : Config} {id : ThreadId} {channel : Channel}
    {destination : L1.Loc} {next : Command}
    (thread : c.threads.lookup id = some (.receive channel destination next))
    (empty : c.queues channel = []) : ∀ after, ¬ Step c id after := by
  intro after step
  cases step with
  | runStep found _ | runDone found | fork found _ _ | join found _ _ | send found _ =>
      simp [thread] at found
  | receive found _ queued =>
      rw [thread] at found
      cases found
      simp [empty] at queued

theorem join_waits {c : Config} {id child : ThreadId} {handle : L1.Loc} {next : Command}
    (thread : c.threads.lookup id = some (.join handle next))
    (target : L1.Store.lookup c.store handle = some (Int.ofNat child))
    (unfinished : c.threads.lookup child ≠ some .done) : ∀ after, ¬ Step c id after := by
  intro after step
  cases step with
  | runStep found _ | runDone found | fork found _ _ | send found _ | receive found _ _ =>
      simp [thread] at found
  | join found otherTarget finished =>
      rw [thread] at found
      cases found
      rw [target] at otherTarget
      cases otherTarget
      exact unfinished finished

end Silmaril.Courses.Cambridge.Concurrency.UnixThreads
