module

import Silmaril.Machine.SQLite.GlobalState.All

namespace Silmaril.Machine.SQLite.GlobalState.AggregateChecks

private def vfs : LocalId .vfs := ⟨0⟩
private def fields : VfsFields := ⟨"fixture", 120, 512⟩
private def structs := IndexedStore.empty.insert vfs fields
private def flat := structs.toFlat
private def objects := flat.toIndexed.toObjects (fun _ => .live)
private def kinds := objects.toStates.toKinds

private theorem hasVfs : kinds.HasKind vfs.tagged .vfs := by
  rw [ObjectStore.HasKind, kinds, objects, FlatStore.lookup_toStates_toKinds, flat,
    IndexedStore.lookup_toFlat]
  rfl

private def registration : kinds.Ref .vfs := ⟨vfs.tagged, hasVfs⟩
private def roots : VfsRoots kinds := ⟨[registration], by simp⟩

example : flat.toIndexed.lookup vfs.tagged.localId = structs.lookup vfs.tagged.localId :=
  (flat.lookup_toIndexed vfs.tagged).trans (structs.lookup_toFlat vfs.tagged)

-- The typed payload survives the flat-store bridge, and its erasure
-- supports the same VFS root at the original tag.
example : objects.lookup vfs.tagged = some ⟨.vfs, .live, fields⟩ := by
  rw [objects, FlatStore.lookup_toObjects, flat, IndexedStore.lookup_toFlat]
  rfl

example : roots.defaultVfs.map Subtype.val = some vfs.tagged := rfl

private abbrev FixtureFields := Handle.Payload TaggedId Unit LocalFields
private def emptyHistory : History TaggedId FixtureFields := History.empty
private theorem freshVfs : emptyHistory.Fresh vfs.tagged := History.lookup_empty vfs.tagged

private def history := emptyHistory.allocate vfs.tagged .vfs fields freshVfs

private abbrev AllocationFixture := Allocator.State TaggedId TaggedId FixtureFields Unit Unit
private def scope : Allocator.Scope Unit Unit := ⟨(), (), 64, by decide⟩
private def block := scope.block 64 128 (by decide) (by decide)
private def before : AllocationFixture := ⟨history, ∅⟩
private def combined : AllocationFixture := before.writeAllocation vfs.tagged (.live block)

private def alloc : Semantics.Resource.Contract AllocationFixture
    (Allocator.Call TaggedId) (Allocator.Reply TaggedId) (StoreId TaggedId TaggedId) :=
  Allocator.contract scope

private theorem allocated : alloc.step (.malloc 64) before (.pointer (some vfs.tagged)) combined :=
  .mallocSuccess (by decide) (by decide) (by decide) (AllocationHistory.lookup_empty vfs.tagged)

private theorem present : combined.objectHistory.lookup vfs.tagged =
    some (.present ⟨.vfs, .live, fields⟩) :=
  emptyHistory.lookup_allocate_self vfs.tagged .vfs fields freshVfs

private def registry := roots.registered.map Subtype.val

private theorem registered : Handle.Registered registry combined.objectHistory := by
  refine ⟨by simp [registry, roots], ?_⟩
  intro id member
  have same : id = vfs.tagged := by simpa [registry, roots, registration] using member
  subst id
  exact ⟨fields, present⟩

private def handles : Semantics.Resource.Contract AllocationFixture
    (Handle.Call TaggedId) (Handle.Reply TaggedId) (StoreId TaggedId TaggedId) :=
  Handle.contract () registry

private theorem borrowed :
    handles.step .findDefaultVfs combined (.borrowedVfs (some vfs.tagged)) combined :=
  ⟨.findDefaultVfs registered, rfl⟩

private def mallocThenBorrow := alloc.seq handles fun _ _ => .findDefaultVfs

private theorem composed :
    mallocThenBorrow.step (.malloc 64) before
      (.pointer (some vfs.tagged), .borrowedVfs (some vfs.tagged)) combined :=
  ⟨combined, allocated, borrowed⟩

-- Malloc issues a raw token whose value coincides with the already visible VFS.
example : combined.lookup (.allocation vfs.tagged) = some (.allocation (.live block)) := by
  change (combined.lookupAllocation vfs.tagged).map StoreEntry.allocation = _
  rw [combined, Allocator.lookup_write_self]
  rfl

-- Both contracts use the tagged observation, so the borrow still sees the
-- live object even though the same value was written to the raw lane.
example : combined.lookup (.object vfs.tagged) = before.lookup (.object vfs.tagged) := by
  have frames : mallocThenBorrow.Frames AllocatorStore.lookup :=
    Semantics.Resource.Contract.seq_frames Allocator.frames Handle.frames
  exact frames composed (.object vfs.tagged) (by decide)

example : ∃ payload : LocalFields .vfs, combined.objectHistory.lookup vfs.tagged =
    some (.present ⟨.vfs, .live, payload⟩) :=
  Handle.find_default_live borrowed.1

example : combined.toObjects.lookupTagged (.object vfs.tagged : StoreId TaggedId TaggedId) =
    some ⟨.vfs, .live, fields⟩ := by
  simp [AllocatorStore.toObjects, Objects.lookupTagged, present, HistoryEntry.toObject]

example : (combined.lookup (.allocation vfs.tagged)).bind StoreEntry.toObject = none :=
  (combined.lookup_toObjects (.allocation vfs.tagged)).symm

example : combined.checkObjectId .vfs (.allocation vfs.tagged) = none :=
  combined.checkObjectId_allocation .vfs vfs.tagged

example (main : NamedMainFile) (number : Nat) {files : VFS.FileMap} {grant : Pager.LockGrant}
    {file : SqliteVfs.FileState} (live : main.opened.Live files file main.mode)
    (allowed : grant.Allows main.opened .readOnly) :
    Pager.ReadAccess files main.opened grant file (main.page number) :=
  main.readAccess number live allowed

end Silmaril.Machine.SQLite.GlobalState.AggregateChecks
