module

public import Silmaril.Machine.SQLite.GlobalState.Indexed
public import Std.Data.DHashMap.Basic

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

/-- A single finite map carrying the fields at each tagged key. The key's
kind determines the value type, so an entry agrees with its tag by construction. -/
abbrev FlatStore := Std.DHashMap TaggedId (fun id => LocalFields id.kind)

namespace FlatStore

abbrev Entry := (id : TaggedId) × LocalFields id.kind

def ofEntries (entries : List Entry) : FlatStore :=
  entries.foldr (fun entry store => store.insert entry.1 entry.2) ∅

def indexEntries (entries : List Entry) : IndexedStore :=
  entries.foldr (fun entry store => store.insert entry.1.localId entry.2) IndexedStore.empty

def toIndexed (store : FlatStore) : IndexedStore :=
  indexEntries store.toList

end FlatStore

def IndexedStore.flatEntries (store : IndexedStore) : List FlatStore.Entry :=
  store.taggedKeys.filterMap fun id => (store.lookup id.localId).map (Sigma.mk id)

def IndexedStore.toFlat (store : IndexedStore) : FlatStore :=
  FlatStore.ofEntries store.flatEntries

end Silmaril.Machine.SQLite.GlobalState
