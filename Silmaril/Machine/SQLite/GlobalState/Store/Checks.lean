module

import Silmaril.Machine.SQLite.GlobalState.Store.Thms
import Std.Data.ExtHashMap.Lemmas

namespace Silmaril.Machine.SQLite.GlobalState.Store.Checks

private def Payload : ObjectKind → Type
  | .connection => Option Nat
  | .pager => Nat
  | _ => Unit

private def zombie : Object Payload := ⟨.connection, .zombie, none⟩

private def entries : List (Nat × HistoryEntry Payload) := [
  (0, .present zombie),
  (1, .present ⟨.file, .live, ()⟩),
  (2, .present ⟨.pager, .live, (512 : Nat)⟩),
  (3, .present ⟨.btree, .live, ()⟩),
  (4, .present ⟨.pageCache, .live, ()⟩),
  (5, .present ⟨.vfs, .live, ()⟩),
  (6, .freed .statement)]

private def snapshot : History Nat Payload := Std.ExtHashMap.ofList entries
private def objects := snapshot.toObjects
private def kinds := objects.toKinds

private theorem lookup_snapshot (id : Nat) :
    snapshot.lookup id = entries.findSomeRev? (fun (key, entry) =>
      if key == id then some entry else none) := by
  rw [History.lookup, snapshot, Std.ExtHashMap.get?_eq_getElem?,
    Std.ExtHashMap.ofList_eq_insertMany_empty, Std.ExtHashMap.getElem?_insertMany_list]
  simp

private theorem lookup_zombie : objects.lookup 0 = some zombie := by
  rw [objects, History.lookup_toObjects, lookup_snapshot]
  rfl

-- The object persists even though its reference field is null.
example : (objects.lookup 0).map (fun object =>
    (object.kind, object.state)) = some (.connection, .zombie) := by
  rw [lookup_zombie]
  rfl

example : zombie.payload = (none : Option Nat) := rfl

example : (objects.toStates.lookup 0).map Object.state = some .zombie := by
  rw [Objects.toStates, Objects.lookup_map, lookup_zombie]
  rfl

example : objects.lookupLive 0 = none := by
  rw [Objects.lookupLive, lookup_zombie]
  rfl

example : ((objects.checkId .publicHandles 0).map Subtype.val) = some 0 := by
  simp [Objects.checkId, Objects.lookupSupported, lookup_zombie, zombie, KindView.supports]
  rfl

private def db : objects.PresentId .publicHandles :=
  ⟨0, by simp [Objects.lookupSupported, lookup_zombie, zombie, KindView.supports]⟩

example : (kinds.restrict .publicHandles).lookup db.val = some (objects.get .publicHandles db).kind :=
  objects.lookup_kind_get .publicHandles db

example : (objects.get .publicHandles db).state = .zombie := by
  have found := objects.lookup_get .publicHandles db
  change objects.lookup 0 = _ at found
  rw [lookup_zombie] at found
  rw [← Option.some.inj found]
  rfl

example : (objects.checkId .vfs 0).isNone = true := by
  simp [Objects.checkId, Objects.lookupSupported, lookup_zombie, zombie, KindView.supports]

example : (objects.checkId .publicHandles 6).isSome = false := by
  rw [Objects.checkId_isSome, ObjectStore.lookup_restrict, Objects.lookup_toKinds,
    objects, History.lookup_toObjects, lookup_snapshot]
  decide

example : (objects.checkId .publicHandles 7).isSome = false := by
  rw [Objects.checkId_isSome, ObjectStore.lookup_restrict, Objects.lookup_toKinds,
    objects, History.lookup_toObjects, lookup_snapshot]
  decide

-- File and Pager membership overlaps the adjacent component policies.
example : (kinds.restrict .vfs).lookup 1 = some .file ∧
    (kinds.restrict .cache).lookup 1 = some .file := by
  simp only [kinds, ObjectStore.lookup_restrict, Objects.lookup_toKinds, objects,
    History.lookup_toObjects, lookup_snapshot]
  decide

example : (kinds.restrict .cache).lookup 2 = some .pager ∧
    (kinds.restrict .btree).lookup 2 = some .pager := by
  simp only [kinds, ObjectStore.lookup_restrict, Objects.lookup_toKinds, objects,
    History.lookup_toObjects, lookup_snapshot]
  decide

example : (kinds.restrict .btree).lookup 4 = none ∧
    (kinds.restrict .cache).lookup 4 = some .pageCache := by
  simp only [kinds, ObjectStore.lookup_restrict, Objects.lookup_toKinds, objects,
    History.lookup_toObjects, lookup_snapshot]
  decide

private def initial : StateHistory Nat := History.empty
private theorem initialFresh : initial.Fresh 7 := History.lookup_empty 7
private def allocated := initial.allocate 7 .connection () initialFresh

private theorem allocation : allocated.lookup 7 = some (.present ⟨.connection, .live, ()⟩) :=
  initial.lookup_allocate_self 7 .connection () initialFresh

private def released := allocated.free 7 allocation

example : released.lookup 7 = some (.freed .connection) := by simp [released]

example : released.toObjects = allocated.toObjects.erase 7 :=
  allocated.toObjects_free 7 allocation

private theorem releasedFresh : released.Fresh 8 := by
  rw [released, History.fresh_free_iff, allocated, History.fresh_allocate_iff]
  simp [History.Fresh, initial]

example : (released.toObjects.toKinds.lookup 7, released.toObjects.toKinds.lookup 8) =
    (none, none) := by
  have neverBound : released.lookup 8 = none := releasedFresh
  simp only [Objects.lookup_toKinds, History.lookup_toObjects, neverBound]
  rw [show released.lookup 7 = some (.freed .connection) by simp [released]]
  rfl

example : ¬ released.Fresh 7 := by
  rw [released, History.fresh_free_iff, allocated, History.fresh_allocate_iff]
  simp

#print axioms ObjectStore.lookup_restrict
#print axioms Objects.lookup_map
#print axioms Objects.lookup_toKinds
#print axioms Objects.lookup_restrict
#print axioms Objects.toKinds_map
#print axioms Objects.map_restrict
#print axioms Objects.toKinds_restrict
#print axioms Objects.checkId_isSome
#print axioms Objects.lookup_get
#print axioms Objects.lookup_kind_get
#print axioms History.lookup_empty
#print axioms History.lookup_map
#print axioms History.lookup_toObjects
#print axioms History.toObjects_map
#print axioms History.lookup_allocate_self
#print axioms History.lookup_free_self
#print axioms History.fresh_allocate_iff
#print axioms History.fresh_free_iff
#print axioms History.toObjects_free
#print axioms History.toObjects_not_injective

end Silmaril.Machine.SQLite.GlobalState.Store.Checks
