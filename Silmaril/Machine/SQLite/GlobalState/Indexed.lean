module

public import Silmaril.Machine.SQLite.GlobalState.Structs

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

/-- One finite map per kind. The map for a given kind uses the slot component
of its local IDs. -/
structure IndexedStore where
  byKind : (kind : ObjectKind) → Std.ExtTreeMap Nat (LocalFields kind)

namespace IndexedStore

def empty : IndexedStore := ⟨fun _ => ∅⟩

def lookup (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind) :
    Option (LocalFields kind) :=
  (store.byKind kind).get? id.slot

/-- Replace one per-kind map, leaving every other kind's map in place. -/
def setMap (store : IndexedStore) (kind : ObjectKind)
    (entries : Std.ExtTreeMap Nat (LocalFields kind)) : IndexedStore :=
  ⟨fun other => if h : kind = other then h ▸ entries else store.byKind other⟩

def insert (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind)
    (fields : LocalFields kind) : IndexedStore :=
  store.setMap kind ((store.byKind kind).insert id.slot fields)

def erase (store : IndexedStore) {kind : ObjectKind} (id : LocalId kind) : IndexedStore :=
  store.setMap kind ((store.byKind kind).erase id.slot)

def kinds : List ObjectKind :=
  [.connection, .statement, .blob, .backup, .vfs, .file, .pageCache, .pager, .btree]

def taggedKeys (store : IndexedStore) : List TaggedId :=
  kinds.flatMap fun kind => (store.byKind kind).keys.map (TaggedId.mk kind)

/-- Construct the kind-only store from tagged keys, with each key's own kind
as its value. -/
def kindsOfKeys (keys : List TaggedId) : ObjectStore TaggedId :=
  keys.foldr (fun id store => store.insert id id.kind) ObjectStore.empty

def erasePayloads (store : IndexedStore) : ObjectStore TaggedId :=
  kindsOfKeys store.taggedKeys

end IndexedStore

end Silmaril.Machine.SQLite.GlobalState
