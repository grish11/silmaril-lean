module

public import Silmaril.Semantics.Resource.Defs
public import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Defs

/-! Resource-level contracts for SQLite's public allocation family. -/

@[expose] public section

namespace Silmaril.Machine.SQLite.Allocator

open GlobalState

universe u v p f o

/-- The live allocation metadata. The requested extent is positive and lies
within the extent reported by the allocation implementation. -/
structure Block (Family : Type f) (Owner : Type o) where
  family : Family
  owner : Owner
  requested : Nat
  usable : Nat
  requested_pos : 0 < requested
  requested_le_usable : requested ≤ usable
  deriving DecidableEq, Repr

/-- The default and maximum build-time value of `SQLITE_MAX_ALLOCATION_SIZE`. -/
def maxAllocationSize : Nat := 2147483391

/-- Which allocator implementation and owner the caller is authorized to use,
with the request limit for this initialized profile. -/
structure Scope (Family : Type f) (Owner : Type o) where
  family : Family
  owner : Owner
  maxRequest : Nat
  maxRequest_supported : maxRequest ≤ maxAllocationSize

def Scope.Owns {Family : Type f} {Owner : Type o}
    (scope : Scope Family Owner) (block : Block Family Owner) : Prop :=
  block.family = scope.family ∧ block.owner = scope.owner

def Scope.block {Family : Type f} {Owner : Type o} (scope : Scope Family Owner)
    (request : Int) (usable : Nat) (positive : 0 < request)
    (fits : request.toNat ≤ usable) : Block Family Owner :=
  ⟨scope.family, scope.owner, request.toNat, usable, Int.pos_iff_toNat_pos.mp positive, fits⟩

/-- Pointers are either null or abstract allocation identities. -/
inductive Call (Id : Type u) where
  | malloc (request : Int)
  | free (pointer : Option Id)
  | realloc (pointer : Option Id) (request : Int)
  deriving DecidableEq, Repr

inductive Reply (Id : Type u) where
  | pointer (value : Option Id)
  | freed
  deriving DecidableEq, Repr

/-- A footprint computed from the public call and its reply. A nonpositive
resize can retire its input even though the returned pointer is null. -/
def writes {Id : Type u} : Call Id → Reply Id → List Id
  | .malloc _, .pointer pointer
  | .realloc none _, .pointer pointer => pointer.toList
  | .free (some id), .freed => [id]
  | .realloc (some old) _, .pointer (some new) => [old, new]
  | .realloc (some id) request, .pointer none => if request ≤ 0 then [id] else []
  | _, _ => []

/-- The shared finite store, using full block metadata while live and a
reserved token with unit metadata after retirement. -/
abbrev State (ObjectId : Type v) [BEq ObjectId] [Hashable ObjectId]
    (Id : Type u) [BEq Id] [Hashable Id] (Payload : ObjectKind → Type p)
    (Family : Type f) (Owner : Type o) :=
  AllocatorStore ObjectId Id Payload (Block Family Owner) Unit

variable {ObjectId : Type v} [BEq ObjectId] [Hashable ObjectId]
  {Id : Type u} [BEq Id] [Hashable Id] [LawfulBEq Id]
  {Payload : ObjectKind → Type p} {Family : Type f} {Owner : Type o}

def State.lookupAllocation (state : State ObjectId Id Payload Family Owner) (id : Id) :
    Option (AllocationEntry (Block Family Owner) Unit) :=
  AllocationHistory.lookup state.allocationHistory id

/-- A single table edit. The transition rules supply the guards for its use. -/
def State.writeAllocation (state : State ObjectId Id Payload Family Owner) (id : Id)
    (entry : AllocationEntry (Block Family Owner) Unit) :
    State ObjectId Id Payload Family Owner :=
  { state with allocationHistory := state.allocationHistory.insert id entry }

/-- Capability to operate on an existing block in this snapshot. -/
def OwnsAt (scope : Scope Family Owner) (state : State ObjectId Id Payload Family Owner)
    (id : Id) (block : Block Family Owner) : Prop :=
  state.lookupAllocation id = some (.live block) ∧ scope.Owns block

/-- Outcomes for initialized public allocator calls. Invalid non-null
arguments have no transition under the supplied family and owner. -/
inductive Step (scope : Scope Family Owner) :
    Call Id → State ObjectId Id Payload Family Owner → Reply Id → State ObjectId Id Payload Family Owner → Prop
  | mallocNonpositive {request before} (nonpositive : request ≤ 0) :
      Step scope (.malloc request) before (.pointer none) before
  | mallocFailure {request before} (positive : 0 < request) :
      Step scope (.malloc request) before (.pointer none) before
  | mallocSuccess {request before id usable}
      (positive : 0 < request) (withinLimit : request.toNat ≤ scope.maxRequest)
      (fits : request.toNat ≤ usable) (fresh : before.lookupAllocation id = none) :
      Step scope (.malloc request) before (.pointer (some id))
        (before.writeAllocation id (.live (scope.block request usable positive fits)))
  | freeNull {before} : Step scope (.free none) before .freed before
  | freeLive {before id block} (owned : OwnsAt scope before id block) :
      Step scope (.free (some id)) before .freed (before.writeAllocation id (.freed ()))
  | reallocNull {request before pointer after}
      (alloc : Step scope (.malloc request) before (.pointer pointer) after) :
      Step scope (.realloc none request) before (.pointer pointer) after
  | reallocNonpositive {request before id block}
      (nonpositive : request ≤ 0) (owned : OwnsAt scope before id block) :
      Step scope (.realloc (some id) request) before (.pointer none) (before.writeAllocation id (.freed ()))
  | reallocFailure {request before id block}
      (positive : 0 < request) (owned : OwnsAt scope before id block) :
      Step scope (.realloc (some id) request) before (.pointer none) before
  | reallocInPlace {request before id block usable}
      (positive : 0 < request) (withinLimit : request.toNat ≤ scope.maxRequest)
      (fits : request.toNat ≤ usable) (owned : OwnsAt scope before id block) :
      Step scope (.realloc (some id) request) before (.pointer (some id))
        (before.writeAllocation id (.live (scope.block request usable positive fits)))
  | reallocMoved {request before old new block usable}
      (positive : 0 < request) (withinLimit : request.toNat ≤ scope.maxRequest)
      (fits : request.toNat ≤ usable) (owned : OwnsAt scope before old block)
      (fresh : before.lookupAllocation new = none) :
      Step scope (.realloc (some old) request) before (.pointer (some new))
        ((before.writeAllocation old (.freed ())).writeAllocation new
          (.live (scope.block request usable positive fits)))

def contract (scope : Scope Family Owner) :
    Semantics.Resource.Contract (State ObjectId Id Payload Family Owner)
      (Call Id) (Reply Id) (StoreId ObjectId Id) where
  step := Step scope
  writes input reply := (writes input reply).map StoreId.allocation

end Silmaril.Machine.SQLite.Allocator
