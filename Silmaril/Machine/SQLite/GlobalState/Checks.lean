module

import Silmaril.Machine.SQLite.GlobalState.Thms

namespace Silmaril.Machine.SQLite.GlobalState.Checks

private def store : ObjectStore String :=
  ((ObjectStore.empty.insert "main" .vfs).insert "db" .connection).insert "alternate" .vfs

example : store.lookup "absent" = none := by
  simp [store, ObjectStore.lookup_insert_of_ne]

example : (store.insert "db" .statement).lookup "db" = some .statement := by simp

example : (store.erase "main").lookup "db" = some .connection := by
  simp [store, ObjectStore.lookup_insert_of_ne, ObjectStore.lookup_erase_of_ne]

example : (store.erase "main").lookup "main" = none := by simp

example : store.erase "absent" = store := by
  apply ObjectStore.ext
  intro id
  by_cases h : id = "absent"
  · subst id
    simp [store, ObjectStore.lookup_insert_of_ne]
  · exact ObjectStore.lookup_erase_of_ne store h

example : ¬ store.HasKind "db" .vfs := by
  simp [ObjectStore.HasKind, store, ObjectStore.lookup_insert_of_ne]

private def alternate : store.Ref .vfs := ⟨"alternate", by simp [ObjectStore.HasKind, store]⟩

private def main : store.Ref .vfs :=
  ⟨"main", by simp [ObjectStore.HasKind, store, ObjectStore.lookup_insert_of_ne]⟩

example : (VfsRoots.mk [] (by simp) : VfsRoots store).defaultVfs = none := rfl

example : (VfsRoots.mk [alternate] (by simp)).defaultVfs = some alternate := rfl

example : (VfsRoots.mk [main, alternate] (by decide)).defaultVfs = some main := rfl

#print axioms ObjectStore.lookup_empty
#print axioms ObjectStore.lookup_insert_self
#print axioms ObjectStore.lookup_insert_of_ne
#print axioms ObjectStore.lookup_erase_self
#print axioms ObjectStore.lookup_erase_of_ne
#print axioms ObjectStore.ext
#print axioms ObjectStore.hasKind_unique

end Silmaril.Machine.SQLite.GlobalState.Checks
