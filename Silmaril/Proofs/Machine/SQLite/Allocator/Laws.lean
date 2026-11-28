module

public import Silmaril.Machine.SQLite.Allocator.Defs
public import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.Allocator

open Silmaril.Machine.SQLite.GlobalState Silmaril.Machine.SQLite.Allocator

universe u v p f o

variable {ObjectId : Type v} [BEq ObjectId] [Hashable ObjectId]
  {Id : Type u} [BEq Id] [Hashable Id] [LawfulBEq Id]
  {Payload : ObjectKind → Type p} {Family : Type f} {Owner : Type o}
  {scope : Scope Family Owner} {before after : State ObjectId Id Payload Family Owner}
  {request : Int} {id : Id} {pointer : Option Id} {reply : Reply Id}

theorem lookup_write_self (state : State ObjectId Id Payload Family Owner) (key : Id)
    (entry : AllocationEntry (Block Family Owner) Unit) :
    (state.writeAllocation key entry).lookupAllocation key = some entry :=
  AllocationHistory.lookup_insert_self state.allocationHistory key entry

theorem lookup_write_of_ne (state : State ObjectId Id Payload Family Owner)
    {key other : Id} (different : other ≠ key) (entry : AllocationEntry (Block Family Owner) Unit) :
    (state.writeAllocation key entry).lookupAllocation other = state.lookupAllocation other :=
  AllocationHistory.lookup_insert_of_ne state.allocationHistory different entry

theorem malloc_success_lookup (h : Step scope (.malloc request) before (.pointer (some id)) after) :
    before.lookupAllocation id = none ∧ 0 < request ∧ request.toNat ≤ scope.maxRequest ∧
      ∃ block, OwnsAt scope after id block ∧ block.requested = request.toNat := by
  cases h with
  | mallocSuccess positive withinLimit fits fresh =>
    exact ⟨fresh, positive, withinLimit, _, ⟨lookup_write_self .., rfl, rfl⟩, rfl⟩

theorem malloc_null_preserves (h : Step scope (.malloc request) before (.pointer none) after) :
    after = before := by cases h <;> rfl

theorem malloc_nonpositive_iff (nonpositive : request ≤ 0) :
    Step scope (.malloc request) before reply after ↔ reply = .pointer none ∧ after = before := by
  constructor
  · intro step
    cases step with
    | mallocNonpositive => exact ⟨rfl, rfl⟩
    | mallocFailure positive | mallocSuccess positive =>
      exact (Int.not_lt_of_ge nonpositive positive).elim
  · rintro ⟨rfl, rfl⟩
    exact .mallocNonpositive nonpositive

theorem free_live_iff :
    Step scope (.free (some id)) before .freed after ↔
      ∃ block, OwnsAt scope before id block ∧ after = before.writeAllocation id (.freed ()) := by
  constructor
  · intro step
    cases step with | freeLive owned => exact ⟨_, owned, rfl⟩
  · rintro ⟨_, owned, rfl⟩
    exact .freeLive owned

theorem free_null_iff : Step scope (.free none) before .freed after ↔ after = before := by
  constructor
  · intro step
    cases step
    rfl
  · rintro rfl
    exact .freeNull

theorem realloc_null_iff :
    Step scope (.realloc none request) before (.pointer pointer) after ↔
      Step scope (.malloc request) before (.pointer pointer) after :=
  ⟨fun step => by cases step with | reallocNull alloc => exact alloc, Step.reallocNull⟩

theorem realloc_nonpositive_iff_free (nonpositive : request ≤ 0) :
    Step scope (.realloc pointer request) before reply after ↔
      reply = .pointer none ∧ Step scope (.free pointer) before .freed after := by
  constructor
  · intro step
    cases step with
    | reallocNull alloc =>
      obtain ⟨replyNull, rfl⟩ := (malloc_nonpositive_iff nonpositive).mp alloc
      exact ⟨replyNull, .freeNull⟩
    | reallocNonpositive _ owned => exact ⟨rfl, .freeLive owned⟩
    | reallocFailure positive | reallocInPlace positive | reallocMoved positive =>
      exact (Int.not_lt_of_ge nonpositive positive).elim
  · rintro ⟨rfl, step⟩
    cases step with
    | freeNull => exact .reallocNull (.mallocNonpositive nonpositive)
    | freeLive owned => exact .reallocNonpositive nonpositive owned

theorem realloc_applicable_iff :
    (∃ reply after, Step scope (.realloc (some id) request) before reply after) ↔
      ∃ block, OwnsAt scope before id block := by
  constructor
  · rintro ⟨reply, after, step⟩
    cases step with
    | reallocNonpositive _ owned | reallocFailure _ owned
    | reallocInPlace _ _ _ owned | reallocMoved _ _ _ owned _ => exact ⟨_, owned⟩
  · rintro ⟨block, owned⟩
    by_cases nonpositive : request ≤ 0
    · exact ⟨_, _, .reallocNonpositive nonpositive owned⟩
    · exact ⟨_, _, .reallocFailure (Int.lt_of_not_ge nonpositive) owned⟩

theorem realloc_failure_preserves (positive : 0 < request)
    (h : Step scope (.realloc (some id) request) before (.pointer none) after) :
    after = before ∧ ∃ block, OwnsAt scope after id block := by
  cases h with
  | reallocNonpositive nonpositive => exact (Int.not_lt_of_ge nonpositive positive).elim
  | reallocFailure _ owned => exact ⟨rfl, _, owned⟩

theorem realloc_success_lookup {old new : Id}
    (h : Step scope (.realloc (some old) request) before (.pointer (some new)) after) :
    0 < request ∧ request.toNat ≤ scope.maxRequest ∧
      (∃ oldBlock, OwnsAt scope before old oldBlock) ∧
      (∃ block, OwnsAt scope after new block ∧ block.requested = request.toNat) ∧
      (new = old ∨ before.lookupAllocation new = none ∧ after.lookupAllocation old = some (.freed ())) := by
  cases h with
  | reallocInPlace positive withinLimit fits owned =>
    exact ⟨positive, withinLimit, ⟨_, owned⟩, ⟨_, ⟨lookup_write_self .., rfl, rfl⟩, rfl⟩,
      .inl rfl⟩
  | reallocMoved positive withinLimit fits owned fresh =>
    have different : old ≠ new := by
      rintro rfl
      have impossible := owned.1.symm.trans fresh
      cases impossible
    exact ⟨positive, withinLimit, ⟨_, owned⟩, ⟨_, ⟨lookup_write_self .., rfl, rfl⟩, rfl⟩,
      .inr ⟨fresh, (lookup_write_of_ne _ different _).trans (lookup_write_self ..)⟩⟩

theorem lookup_preserved {input : Call Id} (step : Step scope input before reply after) :
    ∀ key, key ∉ writes input reply → after.lookupAllocation key = before.lookupAllocation key := by
  induction step with
  | mallocNonpositive | mallocFailure | freeNull | reallocFailure => intros; rfl
  | mallocSuccess =>
    intro key outside
    exact lookup_write_of_ne _ (by simpa [writes] using outside) _
  | freeLive =>
    intro key outside
    exact lookup_write_of_ne _ (by simpa [writes] using outside) _
  | reallocNull _ ih => exact ih
  | reallocNonpositive nonpositive =>
    intro key outside
    exact lookup_write_of_ne _ (by simpa [writes, nonpositive] using outside) _
  | reallocInPlace =>
    intro key outside
    exact lookup_write_of_ne _ (by simpa [writes] using outside) _
  | reallocMoved =>
    intro key outside
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    exact (lookup_write_of_ne _ outside.2 _).trans (lookup_write_of_ne _ outside.1 _)

theorem objects_preserved {input : Call Id} (step : Step scope input before reply after) :
    after.objectHistory = before.objectHistory := by
  induction step <;> first | rfl | assumption

theorem frames [LawfulBEq ObjectId] :
    (contract (ObjectId := ObjectId) (Id := Id) (Payload := Payload) scope).Frames AllocatorStore.lookup := by
  intro input before reply after step key outside
  cases key with
  | object id => simp only [AllocatorStore.lookup, objects_preserved step]
  | allocation id =>
    exact congrArg (Option.map (StoreEntry.allocation (Payload := Payload)))
      (lookup_preserved step id fun written => outside (List.mem_map_of_mem written))

theorem writes_applicable {input : Call Id} (step : Step scope input before reply after)
    {key : Id} (member : key ∈ writes input reply) :
    before.lookupAllocation key = none ∨ ∃ block, OwnsAt scope before key block := by
  induction step with
  | mallocNonpositive | mallocFailure | freeNull => simp [writes] at member
  | mallocSuccess _ _ _ fresh =>
    simp [writes] at member
    subst key
    exact .inl fresh
  | freeLive owned =>
    simp [writes] at member
    subst key
    exact .inr ⟨_, owned⟩
  | reallocNull _ ih => exact ih member
  | reallocNonpositive nonpositive owned =>
    simp [writes, nonpositive] at member
    subst key
    exact .inr ⟨_, owned⟩
  | reallocFailure positive => simp [writes, Int.not_le.mpr positive] at member
  | reallocInPlace _ _ _ owned =>
    simp [writes] at member
    subst key
    exact .inr ⟨_, owned⟩
  | reallocMoved _ _ _ owned fresh =>
    simp [writes] at member
    rcases member with rfl | rfl
    · exact .inr ⟨_, owned⟩
    · exact .inl fresh

theorem tombstone_preserved {input : Call Id} (step : Step scope input before reply after)
    (retired : before.lookupAllocation id = some (.freed ())) : after.lookupAllocation id = some (.freed ()) := by
  refine (lookup_preserved step id ?_).trans retired
  intro member
  rcases writes_applicable step member with fresh | ⟨block, live, _⟩
  · rw [retired] at fresh
    contradiction
  · rw [retired] at live
    cases live

end Silmaril.Proofs.Machine.SQLite.Allocator
