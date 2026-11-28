module

public import Silmaril.Machine.SQLite.GlobalState.Store.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

universe u v p l t

/-- Metadata carried by a live allocation and by its tombstone can differ.
A never-issued allocation ID has no table entry. -/
inductive AllocationEntry (Live : Type l) (Tombstone : Type t) where
  | live (metadata : Live)
  | freed (metadata : Tombstone)
  deriving DecidableEq, Repr

/-- Finite history of raw allocator blocks. Block identity is supplied by the caller. -/
abbrev AllocationHistory (AllocId : Type v) [BEq AllocId] [Hashable AllocId]
    (Live : Type l) (Tombstone : Type t) := Std.ExtHashMap AllocId (AllocationEntry Live Tombstone)

namespace AllocationHistory

variable {AllocId : Type v} [BEq AllocId] [Hashable AllocId] [LawfulBEq AllocId]
variable {Live : Type l} {Tombstone : Type t}

def lookup (history : AllocationHistory AllocId Live Tombstone) (id : AllocId) :
    Option (AllocationEntry Live Tombstone) :=
  Std.ExtHashMap.get? history id

def Fresh (history : AllocationHistory AllocId Live Tombstone) (id : AllocId) : Prop :=
  history.lookup id = none

end AllocationHistory

/-- The tag specifies which identity space a combined lookup observes. -/
inductive StoreId (ObjectId : Type u) (AllocId : Type v) where
  | object (id : ObjectId)
  | allocation (id : AllocId)
  deriving DecidableEq, Repr

inductive StoreEntry (Payload : ObjectKind → Type p) (Live : Type l) (Tombstone : Type t) where
  | object (entry : HistoryEntry Payload)
  | allocation (entry : AllocationEntry Live Tombstone)

def StoreEntry.toObject {Payload : ObjectKind → Type p} {Live : Type l} {Tombstone : Type t} :
    StoreEntry Payload Live Tombstone → Option (Object Payload)
  | .object entry => entry.toObject
  | .allocation _ => none

/-- Object presence and allocator history are independent observations. A resource
contract can relate an object to the block that provides its storage. -/
structure AllocatorStore (ObjectId : Type u) (AllocId : Type v)
    [BEq ObjectId] [Hashable ObjectId] [BEq AllocId] [Hashable AllocId]
    (Payload : ObjectKind → Type p) (Live : Type l) (Tombstone : Type t) where
  objectHistory : History ObjectId Payload
  allocationHistory : AllocationHistory AllocId Live Tombstone

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId] [LawfulBEq ObjectId]
variable {AllocId : Type v} [BEq AllocId] [Hashable AllocId] [LawfulBEq AllocId]
variable {Payload : ObjectKind → Type p} {Live : Type l} {Tombstone : Type t}

/-- Tagged lookup in the objects-only snapshot. Allocation IDs are outside its domain. -/
def Objects.lookupTagged (store : Objects ObjectId Payload) :
    StoreId ObjectId AllocId → Option (Object Payload)
  | .object id => store.lookup id
  | .allocation _ => none

namespace AllocatorStore

def lookup (store : AllocatorStore ObjectId AllocId Payload Live Tombstone) :
    StoreId ObjectId AllocId → Option (StoreEntry Payload Live Tombstone)
  | .object id => (store.objectHistory.lookup id).map StoreEntry.object
  | .allocation id => (store.allocationHistory.lookup id).map StoreEntry.allocation

/-- Project present objects, including zombies, independently of raw allocations. -/
def toObjects (store : AllocatorStore ObjectId AllocId Payload Live Tombstone) :
    Objects ObjectId Payload :=
  store.objectHistory.toObjects

/-- Admit object IDs supported by the given view. The allocation tag cannot
supply a checked object ID even when the underlying ID types coincide. -/
def checkObjectId (store : AllocatorStore ObjectId AllocId Payload Live Tombstone)
    (view : KindView) : StoreId ObjectId AllocId → Option (store.toObjects.PresentId view)
  | .object id => store.toObjects.checkId view id
  | .allocation _ => none

end AllocatorStore

end Silmaril.Machine.SQLite.GlobalState
