module

import Silmaril.Machine.SQLite.GlobalState.StructObservations
import Silmaril.Machine.SQLite.GlobalState.StructThms
import Silmaril.Machine.SQLite.VFS.Thms

namespace Silmaril.Machine.SQLite.GlobalState.StructChecks

open SqliteVfs

private def vfs : LocalId .vfs := ⟨0⟩
private def mainFile : LocalId .file := ⟨0⟩
private def journal : LocalId .file := ⟨1⟩
private def subjournal : LocalId .file := ⟨2⟩
private def pager : LocalId .pager := ⟨0⟩
private def cache : LocalId .pageCache := ⟨0⟩

private def fileFields : FileFields := ⟨some "main.db", some .readOnly⟩
private def pagerFields : PagerFields LocalId := ⟨vfs, cache, mainFile, journal, subjournal, none, 512⟩

private def store : IndexedStore :=
  let store := IndexedStore.empty.insert vfs ⟨"unix", 120, 512⟩
  let store := store.insert cache ⟨∅, none, none⟩
  let store := store.insert mainFile fileFields
  let store := store.insert journal ⟨some "main.db-journal", none⟩
  let store := store.insert subjournal ⟨none, none⟩
  store.insert pager pagerFields

example : vfs.slot = mainFile.slot ∧ vfs.tagged ≠ mainFile.tagged := by decide

example : (store.erase mainFile).lookup mainFile = none := by simp

example : (store.erase mainFile).lookup journal = store.lookup journal :=
  IndexedStore.lookup_erase_of_ne store mainFile journal (by decide)

example : (store.erase mainFile).lookup pager = some pagerFields := by
  rw [IndexedStore.lookup_erase_of_ne store mainFile pager (by decide)]
  exact IndexedStore.lookup_insert_self _ pager pagerFields

example : (store.erase mainFile).erasePayloads.lookup mainFile.tagged = none := by
  rw [IndexedStore.erasePayloads_erase]
  simp

private theorem vfsPresent : store.erasePayloads.lookup vfs.tagged = some .vfs := by
  rw [IndexedStore.lookup_erasePayloads]
  rfl

example : (store.erase mainFile).erasePayloads.lookup vfs.tagged = some .vfs := by
  rw [IndexedStore.erasePayloads_erase, ObjectStore.lookup_erase_of_ne _ (by decide : vfs.tagged ≠ mainFile.tagged)]
  exact vfsPresent

example : ¬store.erasePayloads.HasKind vfs.tagged .file := by
  simp [ObjectStore.HasKind, vfsPresent]

example : ∃ fields : FileFields, store.lookup mainFile = some fields := by
  have h : store.erasePayloads.HasKind mainFile.tagged .file := by
    rw [ObjectStore.HasKind, IndexedStore.lookup_erasePayloads]
    rfl
  exact ((store.hasKind_erasePayloads_iff mainFile.tagged .file).mp h).2

private def opened : VFS.Opened := ⟨"main.db", ⟨7⟩⟩
private def main : NamedMainFile := ⟨opened, .readOnly, 512⟩
private def backing : FileState := ⟨[], none, 7⟩
private def before : VFS.FileMap := fun path => if path = "main.db" then some backing else none
private def after : VFS.FileMap :=
  fun path => if path = "main.db" then some { backing with openMode := some .readOnly } else before path
private def grant : Pager.LockGrant := ⟨opened, .shared⟩

example : store.namedMainFile pager opened.handle = some main := rfl

example : (store.erase mainFile).namedMainFile pager opened.handle = none := rfl

example : ∃ file, Pager.ReadAccess after main.opened grant file (main.page 2) := by
  have success : VFS.openExisting .readOnly 0 false .readOnly "main.db" before = (.ok opened, after) := rfl
  obtain ⟨target, file, _, _, _, bound, _, live, _⟩ := VFS.open_success success
  rw [bound rfl] at live
  exact ⟨_, main.readAccess 2 live ⟨rfl, Or.inl rfl⟩⟩

#print axioms IndexedStore.lookup_empty
#print axioms IndexedStore.lookup_insert_self
#print axioms IndexedStore.lookup_insert_of_ne
#print axioms IndexedStore.lookup_erase_self
#print axioms IndexedStore.lookup_erase_of_ne
#print axioms IndexedStore.lookup_erasePayloads
#print axioms IndexedStore.hasKind_erasePayloads_iff
#print axioms IndexedStore.erasePayloads_insert
#print axioms IndexedStore.erasePayloads_erase
#print axioms NamedMainFile.readAccess

end Silmaril.Machine.SQLite.GlobalState.StructChecks
