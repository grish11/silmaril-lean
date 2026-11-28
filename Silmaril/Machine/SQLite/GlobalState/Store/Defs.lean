module

public import Silmaril.Machine.SQLite.GlobalState.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

universe u v w

/-- The state of a present object. A zombie still has a kind and a payload. -/
inductive PresentState where
  | live
  | zombie
  deriving DecidableEq, Repr

/-- The payload family can be uniform or give each kind its own field type. -/
structure Object (Payload : ObjectKind → Type v) where
  kind : ObjectKind
  state : PresentState
  payload : Payload kind

def Object.map {Payload : ObjectKind → Type v} {Target : ObjectKind → Type w}
    (f : (kind : ObjectKind) → Payload kind → Target kind) (object : Object Payload) :
    Object Target :=
  ⟨object.kind, object.state, f object.kind object.payload⟩

/-- A tombstone retains the allocated kind after the object payload is gone. -/
inductive HistoryEntry (Payload : ObjectKind → Type v) where
  | present (object : Object Payload)
  | freed (kind : ObjectKind)

def HistoryEntry.toObject {Payload : ObjectKind → Type v} :
    HistoryEntry Payload → Option (Object Payload)
  | .present object => some object
  | .freed _ => none

def HistoryEntry.map {Payload : ObjectKind → Type v} {Target : ObjectKind → Type w}
    (f : (kind : ObjectKind) → Payload kind → Target kind) :
    HistoryEntry Payload → HistoryEntry Target
  | .present object => .present (object.map f)
  | .freed kind => .freed kind

/-- Finite snapshot of present objects, including zombies. -/
abbrev Objects (ObjectId : Type u) [BEq ObjectId] [Hashable ObjectId]
    (Payload : ObjectKind → Type v) := Std.ExtHashMap ObjectId (Object Payload)

/-- Finite history of object identities, including live objects, zombies and tombstones.
A missing entry denotes an identity that has never been bound in this history. -/
abbrev History (ObjectId : Type u) [BEq ObjectId] [Hashable ObjectId]
    (Payload : ObjectKind → Type v) := Std.ExtHashMap ObjectId (HistoryEntry Payload)

abbrev StateStore (ObjectId : Type u) [BEq ObjectId] [Hashable ObjectId] :=
  Objects ObjectId (fun _ => Unit)

abbrev StateHistory (ObjectId : Type u) [BEq ObjectId] [Hashable ObjectId] :=
  History ObjectId (fun _ => Unit)

/-- Kind policies for component-facing snapshots. Membership depends on kind alone. -/
inductive KindView where
  | vfs
  | publicHandles
  | cache
  | btree
  deriving DecidableEq, Repr

def KindView.supports : KindView → ObjectKind → Bool
  | .vfs, .vfs | .vfs, .file => true
  | .publicHandles, .connection | .publicHandles, .statement
  | .publicHandles, .blob | .publicHandles, .backup => true
  | .cache, .pageCache | .cache, .pager | .cache, .file => true
  | .btree, .btree | .btree, .pager => true
  | _, _ => false

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId] [LawfulBEq ObjectId]
variable {Payload : ObjectKind → Type v} {Target : ObjectKind → Type w}

def ObjectStore.restrict (store : ObjectStore ObjectId) (view : KindView) :
    ObjectStore ObjectId :=
  Std.ExtHashMap.filter (fun _ kind => view.supports kind) store

namespace Objects

def lookup (store : Objects ObjectId Payload) (id : ObjectId) : Option (Object Payload) :=
  Std.ExtHashMap.get? store id

/-- The live-only observation excludes zombies. Operation-specific guards are separate. -/
def lookupLive (store : Objects ObjectId Payload) (id : ObjectId) : Option (Object Payload) :=
  (store.lookup id).filter fun object => decide (object.state = .live)

def map (store : Objects ObjectId Payload)
    (f : (kind : ObjectKind) → Payload kind → Target kind) : Objects ObjectId Target :=
  Std.ExtHashMap.map (fun _ object => object.map f) store

def toStates (store : Objects ObjectId Payload) : StateStore ObjectId :=
  store.map (fun _ _ => ())

def toKinds (store : Objects ObjectId Payload) : ObjectStore ObjectId :=
  Std.ExtHashMap.map (fun _ object => object.kind) store

def restrict (store : Objects ObjectId Payload) (view : KindView) : Objects ObjectId Payload :=
  Std.ExtHashMap.filter (fun _ object => view.supports object.kind) store

def lookupSupported (store : Objects ObjectId Payload) (view : KindView) (id : ObjectId) :
    Option (Object Payload) :=
  (store.lookup id).filter fun object => view.supports object.kind

/-- Identities present in this finite snapshot with a kind supported by the view.
Both live and zombie entries inhabit this carrier. -/
abbrev PresentId (store : Objects ObjectId Payload) (view : KindView) :=
  {id : ObjectId // (store.lookupSupported view id).isSome}

def checkId (store : Objects ObjectId Payload) (view : KindView) (id : ObjectId) :
    Option (store.PresentId view) :=
  if h : (store.lookupSupported view id).isSome then some ⟨id, h⟩ else none

def get (store : Objects ObjectId Payload) (view : KindView) (id : store.PresentId view) :
    Object Payload :=
  (store.lookupSupported view id.val).get id.property

end Objects

namespace History

def empty : History ObjectId Payload := (∅ : Std.ExtHashMap ObjectId (HistoryEntry Payload))

def lookup (history : History ObjectId Payload) (id : ObjectId) :
    Option (HistoryEntry Payload) :=
  Std.ExtHashMap.get? history id

def Fresh (history : History ObjectId Payload) (id : ObjectId) : Prop :=
  history.lookup id = none

def map (history : History ObjectId Payload)
    (f : (kind : ObjectKind) → Payload kind → Target kind) : History ObjectId Target :=
  Std.ExtHashMap.map (fun _ entry => entry.map f) history

def toStates (history : History ObjectId Payload) : StateHistory ObjectId :=
  history.map (fun _ _ => ())

def toObjects (history : History ObjectId Payload) : Objects ObjectId Payload :=
  Std.ExtHashMap.filterMap (fun _ entry => entry.toObject) history

/-- Record a new live object at an identity never bound in this history. -/
def allocate (history : History ObjectId Payload) (id : ObjectId) (kind : ObjectKind)
    (payload : Payload kind) (_fresh : history.Fresh id) : History ObjectId Payload :=
  Std.ExtHashMap.insert history id (.present ⟨kind, .live, payload⟩)

/-- Replace the state and payload of the current object at this ID, preserving
its kind. Resource contracts supply permissions and allowed state changes. -/
def updatePresent (history : History ObjectId Payload) (id : ObjectId) {object : Object Payload}
    (_present : history.lookup id = some (.present object)) (state : PresentState)
    (payload : Payload object.kind) : History ObjectId Payload :=
  Std.ExtHashMap.insert history id (.present ⟨object.kind, state, payload⟩)

/-- Retire a present object, retaining its kind and reserving its identity. -/
def free (history : History ObjectId Payload) (id : ObjectId) {object : Object Payload}
    (_present : history.lookup id = some (.present object)) : History ObjectId Payload :=
  Std.ExtHashMap.insert history id (.freed object.kind)

end History

end Silmaril.Machine.SQLite.GlobalState
