module

public import Silmaril.Machine.SQLite.GlobalState.Roots
import Std.Data.ExtHashMap.Lemmas

public section

namespace Silmaril.Machine.SQLite.GlobalState.ObjectStore

universe u

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId] [LawfulBEq ObjectId]

@[simp] theorem lookup_empty (id : ObjectId) : (empty : ObjectStore ObjectId).lookup id = none := by
  simp [empty, lookup]

@[simp] theorem lookup_insert_self (store : ObjectStore ObjectId) (id : ObjectId) (kind : ObjectKind) :
    (store.insert id kind).lookup id = some kind :=
  Std.ExtHashMap.getElem?_insert_self (m := store)

theorem lookup_insert_of_ne (store : ObjectStore ObjectId) {id other : ObjectId} (h : other ≠ id)
    (kind : ObjectKind) : (store.insert id kind).lookup other = store.lookup other :=
  (Std.ExtHashMap.getElem?_insert (m := store)).trans (ite_eq_right (by simpa using Ne.symm h))

@[simp] theorem lookup_erase_self (store : ObjectStore ObjectId) (id : ObjectId) :
    (store.erase id).lookup id = none :=
  Std.ExtHashMap.getElem?_erase_self (m := store)

theorem lookup_erase_of_ne (store : ObjectStore ObjectId) {id other : ObjectId} (h : other ≠ id) :
    (store.erase id).lookup other = store.lookup other :=
  (Std.ExtHashMap.getElem?_erase (m := store)).trans (ite_eq_right (by simpa using Ne.symm h))

@[ext] theorem ext {left right : ObjectStore ObjectId}
    (h : ∀ id, left.lookup id = right.lookup id) : left = right :=
  Std.ExtHashMap.ext_getElem? h

theorem hasKind_unique {store : ObjectStore ObjectId} {id : ObjectId} {first second : ObjectKind}
    (hfirst : store.HasKind id first) (hsecond : store.HasKind id second) : first = second :=
  Option.some.inj (hfirst.symm.trans hsecond)

end Silmaril.Machine.SQLite.GlobalState.ObjectStore
