module

public import Silmaril.Machine.SQLite.GlobalState.Flat.Defs
import Silmaril.Proofs.Machine.SQLite.GlobalState.Flat.Lookup

public section

namespace Silmaril.Machine.SQLite.GlobalState

@[simp] theorem IndexedStore.lookup_toFlat (store : IndexedStore) (id : TaggedId) :
    store.toFlat.get? id = store.lookup id.localId :=
  Proofs.Machine.SQLite.GlobalState.Flat.lookup_toFlat store id

@[simp] theorem FlatStore.lookup_toIndexed (store : FlatStore) (id : TaggedId) :
    store.toIndexed.lookup id.localId = store.get? id :=
  Proofs.Machine.SQLite.GlobalState.Flat.lookup_toIndexed store id

end Silmaril.Machine.SQLite.GlobalState
