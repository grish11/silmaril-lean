module

public import Silmaril.Machine.SQLite.Allocator.Defs
public import Silmaril.Semantics.Resource.Thms
import Silmaril.Proofs.Machine.SQLite.Allocator.Laws

public section

namespace Silmaril.Machine.SQLite.Allocator

open GlobalState

universe u v p f o

variable {ObjectId : Type v} [BEq ObjectId] [Hashable ObjectId]
  {Id : Type u} [BEq Id] [Hashable Id] [LawfulBEq Id]
  {Payload : ObjectKind → Type p} {Family : Type f} {Owner : Type o}
  {scope : Scope Family Owner} {before after : State ObjectId Id Payload Family Owner}
  {request : Int} {id : Id} {pointer : Option Id} {reply : Reply Id}

/-- The edited allocation key observes the supplied entry. -/
@[simp] theorem lookup_write_self (state : State ObjectId Id Payload Family Owner) (key : Id)
    (entry : AllocationEntry (Block Family Owner) Unit) :
    (state.writeAllocation key entry).lookupAllocation key = some entry :=
  Proofs.Machine.SQLite.Allocator.lookup_write_self state key entry

/-- An edit preserves the full entry at every other allocation key. -/
theorem lookup_write_of_ne (state : State ObjectId Id Payload Family Owner)
    {key other : Id} (different : other ≠ key) (entry : AllocationEntry (Block Family Owner) Unit) :
    (state.writeAllocation key entry).lookupAllocation other = state.lookupAllocation other :=
  Proofs.Machine.SQLite.Allocator.lookup_write_of_ne state different entry

/-- A successful malloc issues a fresh token and records its caller and request. -/
theorem malloc_success_lookup (h : Step scope (.malloc request) before (.pointer (some id)) after) :
    before.lookupAllocation id = none ∧ 0 < request ∧ request.toNat ≤ scope.maxRequest ∧
      ∃ block, OwnsAt scope after id block ∧ block.requested = request.toNat :=
  Proofs.Machine.SQLite.Allocator.malloc_success_lookup h

/-- A null malloc result leaves the entire resource state intact. -/
theorem malloc_null_preserves (h : Step scope (.malloc request) before (.pointer none) after) :
    after = before :=
  Proofs.Machine.SQLite.Allocator.malloc_null_preserves h

/-- A nonpositive malloc can only return null with the input state. -/
theorem malloc_nonpositive_iff (nonpositive : request ≤ 0) :
    Step scope (.malloc request) before reply after ↔ reply = .pointer none ∧ after = before :=
  Proofs.Machine.SQLite.Allocator.malloc_nonpositive_iff nonpositive

/-- Free of a non-null token requires matching live ownership and records retirement. -/
theorem free_live_iff :
    Step scope (.free (some id)) before .freed after ↔
      ∃ block, OwnsAt scope before id block ∧ after = before.writeAllocation id (.freed ()) :=
  Proofs.Machine.SQLite.Allocator.free_live_iff

/-- Free of null has the input state as its only post-state. -/
theorem free_null_iff : Step scope (.free none) before .freed after ↔ after = before :=
  Proofs.Machine.SQLite.Allocator.free_null_iff

/-- Null realloc has exactly the malloc transitions. -/
theorem realloc_null_iff :
    Step scope (.realloc none request) before (.pointer pointer) after ↔
      Step scope (.malloc request) before (.pointer pointer) after :=
  Proofs.Machine.SQLite.Allocator.realloc_null_iff

/-- A nonpositive realloc returns null and has exactly the corresponding free transitions. -/
theorem realloc_nonpositive_iff_free (nonpositive : request ≤ 0) :
    Step scope (.realloc pointer request) before reply after ↔
      reply = .pointer none ∧ Step scope (.free pointer) before .freed after :=
  Proofs.Machine.SQLite.Allocator.realloc_nonpositive_iff_free nonpositive

/-- A non-null realloc has an outcome exactly when the caller owns the live block. -/
theorem realloc_applicable_iff :
    (∃ reply after, Step scope (.realloc (some id) request) before reply after) ↔
      ∃ block, OwnsAt scope before id block :=
  Proofs.Machine.SQLite.Allocator.realloc_applicable_iff

/-- A positive realloc returning null leaves the old block and its owner available. -/
theorem realloc_failure_preserves (positive : 0 < request)
    (h : Step scope (.realloc (some id) request) before (.pointer none) after) :
    after = before ∧ ∃ block, OwnsAt scope after id block :=
  Proofs.Machine.SQLite.Allocator.realloc_failure_preserves positive h

/-- Successful realloc records the new request. A move issues a fresh token
and leaves an allocator tombstone at the old token. -/
theorem realloc_success_lookup {old new : Id}
    (h : Step scope (.realloc (some old) request) before (.pointer (some new)) after) :
    0 < request ∧ request.toNat ≤ scope.maxRequest ∧
      (∃ oldBlock, OwnsAt scope before old oldBlock) ∧
      (∃ block, OwnsAt scope after new block ∧ block.requested = request.toNat) ∧
      (new = old ∨ before.lookupAllocation new = none ∧ after.lookupAllocation old = some (.freed ())) :=
  Proofs.Machine.SQLite.Allocator.realloc_success_lookup h

/-- Every allocation lookup outside the writes stays equal. -/
theorem lookup_preserved {input : Call Id} (step : Step scope input before reply after) :
    ∀ key, key ∉ writes input reply → after.lookupAllocation key = before.lookupAllocation key :=
  Proofs.Machine.SQLite.Allocator.lookup_preserved step

/-- Allocator calls preserve the entire object history. -/
theorem objects_preserved {input : Call Id} (step : Step scope input before reply after) :
    after.objectHistory = before.objectHistory :=
  Proofs.Machine.SQLite.Allocator.objects_preserved step

/-- The present-object projection is preserved by allocator calls. -/
theorem toObjects_preserved [LawfulBEq ObjectId] {input : Call Id}
    (step : Step scope input before reply after) : after.toObjects = before.toObjects :=
  congrArg History.toObjects (objects_preserved step)

/-- The allocator contract frames full tagged resource observations outside its writes. -/
theorem frames [LawfulBEq ObjectId] :
    (contract (ObjectId := ObjectId) (Id := Id) (Payload := Payload) scope).Frames AllocatorStore.lookup :=
  Proofs.Machine.SQLite.Allocator.frames

/-- A written allocation token was fresh or live and owned by the caller. -/
theorem writes_applicable {input : Call Id} (step : Step scope input before reply after)
    {key : Id} (member : key ∈ writes input reply) :
    before.lookupAllocation key = none ∨ ∃ block, OwnsAt scope before key block :=
  Proofs.Machine.SQLite.Allocator.writes_applicable step member

/-- No allocator step can remove or reissue a retired token. -/
theorem tombstone_preserved {input : Call Id} (step : Step scope input before reply after)
    (retired : before.lookupAllocation id = some (.freed ())) : after.lookupAllocation id = some (.freed ()) :=
  Proofs.Machine.SQLite.Allocator.tombstone_preserved step retired

end Silmaril.Machine.SQLite.Allocator
