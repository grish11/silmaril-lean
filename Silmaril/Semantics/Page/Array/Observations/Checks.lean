module

import Silmaril.Semantics.Page.Array.Observations.Thms

namespace Silmaril.Semantics.Page

open ReadWrite

private def initial : Array 2 Nat := fun _ => 1
private def updated : Array 2 Nat := override initial 0 2
private def restored : Array 2 Nat := override updated 0 1

private def same : Trace Nat Nat := [.read 0 1, .write 0 1, .read 0 1]
private def changed : Trace Nat Nat := [.read 0 1, .write 0 2, .read 0 2]
private def restores : Trace Nat Nat := [.read 0 1, .write 0 2, .write 0 1, .read 0 1]
private def stale : Trace Nat Nat := [.read 0 1, .write 0 2, .read 0 1]

private theorem stable_of_reads_one {trace : Trace Nat Nat}
    (allOnes : ∀ value, (0, value) ∈ trace.reads → value = 1) : trace.ReadsStable 0 := by
  intro earlier gap later pair
  exact (allOnes later pair.members.2).trans (allOnes earlier pair.members.1).symm

-- Same-value writes and restorations can both leave the observations stable.
example : same.StableReadAddresses 0 := by
  refine ⟨⟨1, [.write 0 1], 1, [], [], rfl, by simp [Trace.Reads, Trace.reads]⟩, ?_⟩
  apply stable_of_reads_one
  intro value member
  simpa [same, Trace.reads, List.filterMap] using member

example : same.reads.toTrace.run (Array.access 2 Nat) initial = some initial := rfl

example : restores.StableReadAddresses 0 := by
  refine ⟨⟨1, [.write 0 2, .write 0 1], 1, [], [], rfl, by simp [Trace.Reads, Trace.reads]⟩, ?_⟩
  apply stable_of_reads_one
  intro value member
  simpa [restores, Trace.reads, List.filterMap] using member

example : restores.ReadsMatchLastWrite 0 :=
  Array.replays_matchLastWrite (before := initial) (after := restored) (Trace.run_eq_some_iff.mp rfl) 0

example : restores.reads.toTrace.run (Array.access 2 Nat) initial = some initial := rfl

private theorem changedReplay : changed.Replays (Array.access 2 Nat) initial updated :=
  Trace.run_eq_some_iff.mp rfl

-- A genuine change can be both compatible and outside the stable set.
example : changed.LastWriteCompatibleAddresses 0 ∧ ¬ changed.StableReadAddresses 0 := by
  have pair : changed.ConsecutiveReads 0 1 [.write 0 2] 2 :=
    ⟨[], [], rfl, by simp [Trace.Reads, Trace.reads]⟩
  refine ⟨⟨⟨1, _, 2, pair⟩, Array.replays_matchLastWrite changedReplay 0⟩, ?_⟩
  exact fun stable => changed.stable_disjoint_changed stable ⟨1, _, 2, pair, by decide⟩

example : changed.reads.toTrace.run (Array.access 2 Nat) initial = none := rfl

-- The permissive rule accepts equal stale values. The last-write rule rejects them.
example : stale.ReadsStableWithoutWrites 0 ∧ ¬ stale.ReadsMatchLastWrite 0 := by
  refine ⟨Trace.ReadsStable.withoutWrites (stable_of_reads_one ?_), ?_⟩
  · intro value member
    simpa [stale, Trace.reads, List.filterMap] using member
  · intro compatible
    have pair : stale.ConsecutiveReads 0 1 [.write 0 2] 1 :=
      ⟨[], [], rfl, by simp [Trace.Reads, Trace.reads]⟩
    exact (by decide : (1 : Nat) ≠ 2) (compatible pair)

example : stale.run (Array.access 2 Nat) initial = none := rfl

-- The gap rule is vacuous for one read, even when it is out of bounds.
example : ¬ Trace.RepeatedReadAddresses ([.read 2 1] : Trace Nat Nat) 2 := by
  intro repeats
  obtain ⟨pre, earlier, gap, later, post, eq⟩ := Trace.repeatedReadAddresses_iff.mp repeats
  have lengths := congrArg List.length eq
  simp at lengths
  omega

example : Trace.run (Array.access 2 Nat) [.read 2 1] initial = none := rfl

-- A write can initialize backing that the read projection would need.
private def uninitialized : UndefArray 2 Nat := fun _ => none
private def initialized : UndefArray 2 Nat := override uninitialized 0 (some 1)
private def initializes : Trace Nat Nat := [.write 0 1, .read 0 1, .read 0 1]

example : initializes.ReadsMatchLastWrite 0 :=
  UndefArray.replays_matchLastWrite (before := uninitialized) (after := initialized) (Trace.run_eq_some_iff.mp rfl) 0

example : initializes.reads.toTrace.run (UndefArray.access 2 Nat) uninitialized = none := rfl

end Silmaril.Semantics.Page
