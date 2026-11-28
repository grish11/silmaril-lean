module

import Silmaril.Semantics.Page.Array.Thms
import Silmaril.Semantics.ReadWrite.Labelled.Thms

namespace Silmaril.Semantics.Page

open ReadWrite

private def access := UndefArray.access 2 Nat
private def uninit : UndefArray 2 Nat := fun _ => none
private def first : UndefArray 2 Nat := override uninit (0 : Fin 2) (some 1)
private def second : UndefArray 2 Nat := override first (0 : Fin 2) (some 2)
private def total : Array 2 Nat := fun _ => 1

private def initializes : Trace Nat Nat := [.write 0 1, .read 0 1]
private def updates : Trace Nat Nat := [.read 0 1, .write 0 2, .read 0 2]

example : initializes.run access uninit = some first := rfl
example : updates.run access first = some second := rfl

example : (Trace.run access [.read 0 1] uninit) = none := rfl
example : (Trace.run access [.write 0 1, .read 0 2] uninit) = none := rfl
example : (Trace.run access [.write 2 1] uninit) = none := rfl

example : (Trace.run (Array.access 2 Nat) [.read 0 1] (uninit.complete total)) =
    some (uninit.complete total) := rfl

example : UndefArray.Satisfiable 2 initializes :=
  ⟨uninit, first, Trace.run_eq_some_iff.mp rfl⟩

example : ¬ (UndefArray.Satisfiable 2 ([.write 2 1] : Trace Nat Nat)) := by
  rintro ⟨initial, final, run⟩
  have bounded := UndefArray.replays_inBounds run 2 (.inr ⟨1, List.mem_cons_self⟩)
  exact (Nat.lt_irrefl 2) bounded

example : ¬ initializes.Uses 0 := fun used => used.1 rfl
example : updates.Uses 0 ∧ updates.Defs 0 := ⟨.inl rfl, ⟨2, List.mem_cons_self⟩⟩

example : updates.reads = [(0, 1), (0, 2)] := rfl
example : updates.writes.toTrace.run access first = some second := rfl
-- The read projection drops the write that supplied its second value.
example : updates.reads.toTrace.run access first = none := rfl

example : (Array.access 2 Nat).labelled.Path total updates
    (override total (0 : Fin 2) 2) :=
  Trace.replays_iff_path.mp (Trace.run_eq_some_iff.mp rfl)

example : updates.run access total.embed = some (Array.embed (override total (0 : Fin 2) 2)) := by
  change updates.run (UndefArray.access 2 Nat) total.embed = _
  rw [Array.run_embed]
  rfl

end Silmaril.Semantics.Page
