module

import Silmaril.Machine.SQLite.Allocator.Thms
import Silmaril.Machine.SQLite.GlobalState.Store.Allocator.Thms

namespace Silmaril.Machine.SQLite.Allocator.Checks

open GlobalState Semantics.Resource

private abbrev Fixture := State Nat Nat (fun _ => Unit) String Nat
private def scope : Scope String Nat := ⟨"sqlite", 1, 64, by decide⟩
private def original : Block String Nat := scope.block 12 16 (by decide) (by decide)
private def resized : Block String Nat := scope.block 20 24 (by decide) (by decide)
private def peer : Block String Nat := scope.block 4 8 (by decide) (by decide)

private def initial : Fixture :=
  { objectHistory := History.empty.allocate 1 .connection () (by simp [History.Fresh])
    allocationHistory := ∅ }

private def start : Fixture := initial.writeAllocation 9 (.live peer)
private def allocated : Fixture := start.writeAllocation 1 (.live original)
private def moved : Fixture := (allocated.writeAllocation 1 (.freed ())).writeAllocation 2 (.live resized)

private theorem start_fresh (id : Nat) (hne : id ≠ 9) : start.lookupAllocation id = none := by
  rw [start, lookup_write_of_ne _ hne]
  exact AllocationHistory.lookup_empty id

private theorem malloc_step :
    Step scope (.malloc 12) start (.pointer (some 1)) allocated :=
  .mallocSuccess (by decide) (by decide) (by decide) (start_fresh 1 (by decide))

private theorem old_owned : OwnsAt scope allocated 1 original :=
  ⟨lookup_write_self .., rfl, rfl⟩

private theorem move_step :
    Step scope (.realloc (some 1) 20) allocated (.pointer (some 2)) moved :=
  .reallocMoved (by decide) (by decide) (by decide) old_owned
    ((lookup_write_of_ne start (by decide) _).trans (start_fresh 2 (by decide)))

private theorem old_retired : moved.lookupAllocation 1 = some (.freed ()) :=
  ((realloc_success_lookup move_step).2.2.2.2.resolve_left (by decide)).2

example : Step scope (.malloc (-3)) start (.pointer none) start :=
  .mallocNonpositive (by decide)

example : Step scope (.malloc 17) start (.pointer none) start :=
  .mallocFailure (by decide)

example : Step scope (.free none) start .freed start := .freeNull

example : Step scope (.realloc none 12) start (.pointer (some 1)) allocated :=
  realloc_null_iff.mpr malloc_step

example : Step scope (.free (some 1)) allocated .freed (allocated.writeAllocation 1 (.freed ())) :=
  .freeLive old_owned

example : Step scope (.realloc (some 1) (-1)) allocated (.pointer none)
    (allocated.writeAllocation 1 (.freed ())) :=
  (realloc_nonpositive_iff_free (by decide)).mpr ⟨rfl, .freeLive old_owned⟩

example : Step scope (.realloc (some 1) 20) allocated (.pointer (some 1))
    (allocated.writeAllocation 1 (.live resized)) :=
  .reallocInPlace (by decide) (by decide) (by decide) old_owned

example : ∀ after, Step scope (.realloc (some 1) 20) allocated (.pointer none) after →
    after = allocated ∧ ∃ block, OwnsAt scope after 1 block :=
  fun _ step => realloc_failure_preserves (by decide) step

example : Step scope (.realloc (some 1) 65) allocated (.pointer none) allocated :=
  .reallocFailure (by decide) old_owned

example (after : Fixture) :
    ¬ Step scope (.realloc (some 1) 65) allocated (.pointer (some 2)) after :=
  fun step => (by decide : ¬ (65 : Int).toNat ≤ scope.maxRequest)
    (realloc_success_lookup step).2.1

example (after : Fixture) : ¬ Step scope (.free (some 1)) moved .freed after := by
  intro step
  obtain ⟨block, live, _⟩ := free_live_iff.mp step
  have impossible := old_retired.symm.trans live.1
  cases impossible

example (after : Fixture) : ¬ Step scope (.malloc 12) moved (.pointer (some 1)) after := by
  intro step
  have impossible := old_retired.symm.trans (malloc_success_lookup step).1
  cases impossible

example : ¬ ∃ reply after, Step scope (.realloc (some 8) 20) start reply after := by
  rw [realloc_applicable_iff]
  rintro ⟨block, live, _⟩
  rw [start_fresh 8 (by decide)] at live
  cases live

example (after : Fixture) :
    ¬ Step { scope with owner := 2 } (.free (some 1)) allocated .freed after := by
  intro step
  obtain ⟨block, owned, _⟩ := free_live_iff.mp step
  have same := Option.some.inj ((lookup_write_self start 1 _).symm.trans owned.1)
  cases same
  exact (by decide : (1 : Nat) ≠ 2) owned.2.2

example : ¬ ∃ reply after,
    Step { scope with family := "other" } (.realloc (some 1) 20) allocated reply after := by
  rw [realloc_applicable_iff]
  rintro ⟨block, owned⟩
  have same := Option.some.inj ((lookup_write_self start 1 _).symm.trans owned.1)
  cases same
  exact (by decide : "sqlite" ≠ "other") owned.2.1

private def next (_ : Call Nat) : Reply Nat → Call Nat
  | .pointer pointer => .realloc pointer 20
  | .freed => .free none

private def twoCalls : Contract Fixture (Call Nat) (Reply Nat × Reply Nat) (StoreId Nat Nat) :=
  (contract scope).seq (contract scope) next

private theorem two_steps :
    twoCalls.step (.malloc 12) start (.pointer (some 1), .pointer (some 2)) moved :=
  ⟨allocated, malloc_step, move_step⟩

private theorem two_frames : twoCalls.Frames AllocatorStore.lookup :=
  Contract.seq_frames frames frames

private def hasConnection (state : Fixture) : Prop :=
  state.lookup (.object 1) = some (.object (.present ⟨.connection, .live, ()⟩))

example : hasConnection moved := by
  have reads : DependsOn AllocatorStore.lookup [.object 1] hasConnection := by
    intro before after agrees
    unfold hasConnection
    rw [agrees _ (by simp)]
  apply (two_frames.assertion_iff two_steps reads (by
    intro key member
    simp only [List.mem_singleton] at member
    subst key
    decide)).mp
  simp [hasConnection, AllocatorStore.lookup, start, initial, State.writeAllocation]
  exact History.lookup_allocate_self (Payload := fun _ => Unit) History.empty 1 .connection ()
    (by simp [History.Fresh])

example : moved.lookup (.allocation 9) = some (.allocation (.live peer)) :=
  (two_frames two_steps (.allocation 9) (by decide)).trans
    (congrArg (Option.map (StoreEntry.allocation (Payload := fun _ => Unit))) (lookup_write_self ..))

#print axioms Contract.seq_frames
#print axioms Contract.Frames.assertion_iff
#print axioms lookup_write_self
#print axioms lookup_write_of_ne
#print axioms malloc_success_lookup
#print axioms malloc_null_preserves
#print axioms malloc_nonpositive_iff
#print axioms free_live_iff
#print axioms free_null_iff
#print axioms realloc_null_iff
#print axioms realloc_nonpositive_iff_free
#print axioms realloc_applicable_iff
#print axioms realloc_failure_preserves
#print axioms realloc_success_lookup
#print axioms lookup_preserved
#print axioms objects_preserved
#print axioms toObjects_preserved
#print axioms frames
#print axioms writes_applicable
#print axioms tombstone_preserved

end Silmaril.Machine.SQLite.Allocator.Checks
