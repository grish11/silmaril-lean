module

public import Silmaril.Machine.SQLite.GlobalState.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.GlobalState

universe u

variable {ObjectId : Type u} [BEq ObjectId] [Hashable ObjectId] [LawfulBEq ObjectId]

/-- The ordered VFS registrations in an object store snapshot. Other VFS
objects can be present in the store without being registered. -/
structure VfsRoots (store : ObjectStore ObjectId) where
  registered : List (store.Ref .vfs)
  nodup : registered.Nodup

/-- An unnamed VFS lookup observes the first registration, if any. -/
def VfsRoots.defaultVfs {store : ObjectStore ObjectId} (roots : VfsRoots store) :
    Option (store.Ref .vfs) :=
  roots.registered.head?

end Silmaril.Machine.SQLite.GlobalState
