module

import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Thms

namespace Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Checks

private def Payload : ObjectKind → Type
  | .connection => Option Nat
  | _ => Unit

private def emptyHistory : History Nat Payload := History.empty

private theorem fresh : emptyHistory.Fresh 4 := History.lookup_empty 4

private def history := emptyHistory.allocate 4 .connection (some 11) fresh

private theorem present : history.lookup 4 = some (.present ⟨.connection, .live, some 11⟩) :=
  emptyHistory.lookup_allocate_self 4 .connection (some 11) fresh

private def liveBlocks : AllocationHistory Nat Nat Unit :=
  (∅ : AllocationHistory Nat Nat Unit).insert 4 (.live 64)

private def blocks : AllocationHistory Nat Nat Unit := liveBlocks.insert 5 (.freed ())

private def before : AllocatorStore Nat Nat Payload Nat Unit := ⟨history, blocks⟩

private def after : AllocatorStore Nat Nat Payload Nat Unit :=
  { before with objectHistory := history.updatePresent 4 present .zombie none }

private theorem updated : after.objectHistory.lookup 4 =
    some (.present ⟨.connection, .zombie, none⟩) :=
  history.lookup_updatePresent_self 4 present .zombie none

-- The object and raw allocation deliberately have the same underlying ID value.
example : before.lookup (.allocation 4) = some (.allocation (.live 64)) := by
  change (blocks.lookup 4).map StoreEntry.allocation = _
  rw [blocks, liveBlocks.lookup_insert_of_ne (show (4 : Nat) ≠ 5 by decide)]
  simp [liveBlocks]

example : before.lookup (.allocation 5) = some (.allocation (.freed ())) := by
  simp [AllocatorStore.lookup, before, blocks]

example : before.lookup (.allocation 6) = none := by
  change (blocks.lookup 6).map StoreEntry.allocation = _
  rw [blocks, liveBlocks.lookup_insert_of_ne (show (6 : Nat) ≠ 5 by decide),
    liveBlocks, AllocationHistory.lookup_insert_of_ne ∅ (show (6 : Nat) ≠ 4 by decide)]
  simp

example : after.lookup (.allocation 4) = before.lookup (.allocation 4) := rfl

example : after.lookup (.object 4) = some (.object (.present ⟨.connection, .zombie, none⟩)) := by
  simp [AllocatorStore.lookup, updated]

example : after.toObjects.lookupTagged (.object 4 : StoreId Nat Nat) =
    some ⟨.connection, .zombie, none⟩ := by
  simp [AllocatorStore.toObjects, Objects.lookupTagged, updated, HistoryEntry.toObject]

example : (after.lookup (.allocation 4)).bind StoreEntry.toObject = none :=
  (after.lookup_toObjects (.allocation 4)).symm

example : after.checkObjectId .publicHandles (.allocation 4) = none :=
  after.checkObjectId_allocation .publicHandles 4

example : (after.checkObjectId .publicHandles (.object 4)).isSome = true := by
  simp [AllocatorStore.checkObjectId, Objects.checkId_isSome, AllocatorStore.toObjects,
    updated, HistoryEntry.toObject, KindView.supports]

example : after.objectHistory.lookup 6 = history.lookup 6 :=
  history.lookup_updatePresent_of_ne (show (6 : Nat) ≠ 4 by decide) present .zombie none

example : after.objectHistory.Fresh 6 ↔ history.Fresh 6 :=
  history.fresh_updatePresent_iff 4 6 present .zombie none

#print axioms AllocationHistory.lookup_empty
#print axioms AllocationHistory.lookup_insert_self
#print axioms AllocationHistory.lookup_insert_of_ne
#print axioms AllocatorStore.lookup_toObjects
#print axioms AllocatorStore.checkObjectId_allocation
#print axioms History.lookup_allocate_of_ne
#print axioms History.lookup_updatePresent_self
#print axioms History.lookup_updatePresent_of_ne
#print axioms History.lookup_free_of_ne
#print axioms History.fresh_updatePresent_iff

end Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Checks
