module

import Silmaril.Machine.SQLite.GlobalState.StatePayload
import Std.Data.DHashMap.Lemmas

namespace Silmaril.Machine.SQLite.GlobalState.StatePayloadChecks

private structure NameRef (kind : ObjectKind) where
  name : String

private def namedStatement : ObjectFields NameRef .statement :=
  { connection := ⟨"primary"⟩
    incoming := .predecessorNext ⟨"previous"⟩
    next := none
    sql := none
    btreeCursors := [some ⟨⟨"main tree"⟩, 2, none, []⟩] }

example : namedStatement.connection.name = "primary" := rfl

private def connection : LocalId .connection := ⟨0⟩
private def file : LocalId .file := ⟨0⟩
private def missing : LocalId .file := ⟨1⟩
private def dbFields : ConnectionFields LocalId := ⟨none, none, []⟩
private def fileFields : FileFields := ⟨some "main.db", some .readOnly⟩

private def structs : IndexedStore :=
  (IndexedStore.empty.insert connection dbFields).insert file fileFields

private def state (id : TaggedId) : PresentState :=
  if id = connection.tagged then .zombie else .live

example : (structs.toObjects state).lookup connection.tagged =
    some ⟨.connection, .zombie, dbFields⟩ := by
  rw [IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).lookup file.tagged = some ⟨.file, .live, fileFields⟩ := by
  rw [IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).lookup missing.tagged = none := by
  rw [IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).lookupLive connection.tagged = none := by
  rw [Objects.lookupLive, IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).toStates.lookup connection.tagged =
    some ⟨.connection, .zombie, ()⟩ := by
  rw [Objects.toStates, Objects.lookup_map, IndexedStore.lookup_toObjects]
  rfl

example : (structs.toObjects state).toStates.toKinds.lookup connection.tagged = some .connection := by
  rw [IndexedStore.toObjects_toStates_toKinds, IndexedStore.lookup_erasePayloads]
  rfl

example : (structs.toObjects state).toStates.toKinds = structs.erasePayloads :=
  structs.toObjects_toStates_toKinds state

private def flat : FlatStore := ((∅ : FlatStore).insert connection.tagged dbFields).insert file.tagged fileFields

private theorem flatConnection : flat.get? connection.tagged = some dbFields := by
  have different : ¬(file.tagged == connection.tagged) := by decide
  exact (Std.DHashMap.get?_insert (m := (∅ : FlatStore).insert connection.tagged dbFields)
    (a := connection.tagged) (k := file.tagged) (v := fileFields)).trans
    ((dite_eq_right different).trans Std.DHashMap.get?_insert_self)

private theorem flatFile : flat.get? file.tagged = some fileFields :=
  Std.DHashMap.get?_insert_self

example : flat.toIndexed.lookup connection = some dbFields :=
  (FlatStore.lookup_toIndexed flat connection.tagged).trans flatConnection

example : flat.toIndexed.toFlat.get? file.tagged = some fileFields := by
  rw [IndexedStore.lookup_toFlat, FlatStore.lookup_toIndexed, flatFile]

example : structs.toFlat.toIndexed.lookup missing = none :=
  (FlatStore.lookup_toIndexed structs.toFlat missing.tagged).trans
    ((IndexedStore.lookup_toFlat structs missing.tagged).trans rfl)

example : (flat.toIndexed.toObjects state).lookup connection.tagged =
    some ⟨.connection, .zombie, dbFields⟩ := by
  rw [FlatStore.lookup_toObjects, flatConnection]
  rfl

example : (flat.toIndexed.toObjects state).toStates.toKinds.lookup file.tagged = some .file := by
  rw [FlatStore.lookup_toStates_toKinds, flatFile]
  rfl

#print axioms IndexedStore.lookup_toObjects
#print axioms IndexedStore.toObjects_toKinds
#print axioms IndexedStore.toObjects_toStates_toKinds
#print axioms IndexedStore.lookup_toFlat
#print axioms FlatStore.lookup_toIndexed
#print axioms FlatStore.lookup_toObjects
#print axioms FlatStore.lookup_toStates_toKinds

end Silmaril.Machine.SQLite.GlobalState.StatePayloadChecks
