module

import Silmaril.Machine.SQLite.VirtualMachine.Traced.Thms

namespace Silmaril.Machine.SQLite.VirtualMachine.Traced

open Silmaril.Formats.Sqlite

private def emit : Program := #[.integer 7 1, .resultRow 1 1, .openRead 0 2 0, .halt 0]
private def empty : Database := fun _ _ => none

example : (runWithTrace empty emit 4 initial).report =
    ⟨[.row [.integer 7], .openRead 0 2 false],
      ⟨[[.integer 7]], .fault (.missingTable 0 2)⟩⟩ := rfl

example : ¬ Defined (behaviors {empty} emit 4 initial) := by
  intro defined
  obtain ⟨_, all⟩ := wp_snapshots.mp defined
  exact (by decide : Termination.fault (.missingTable 0 2) ≠ .halted 0) (all empty rfl).1

private def emitPair (a b : Int32) : Program :=
  #[.integer a 1, .resultRow 1 1, .integer b 1, .resultRow 1 1, .halt 0]

example : WP (behaviors {empty} (emitPair 1 2) 5 initial)
    (fun report => report.events = [.row [.integer 1], .row [.integer 2]]) := by
  apply wp_snapshots.mpr
  refine ⟨⟨empty, rfl⟩, ?_⟩
  rintro db (rfl : db = empty)
  exact ⟨rfl, rfl⟩

example : (runWithTrace empty (emitPair 1 2) 5 initial).report ≠
    (runWithTrace empty (emitPair 2 1) 5 initial).report := by decide

end Silmaril.Machine.SQLite.VirtualMachine.Traced
