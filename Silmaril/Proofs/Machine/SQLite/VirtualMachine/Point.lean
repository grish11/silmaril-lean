module

public import Silmaril.Machine.SQLite.VirtualMachine.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine

private theorem seek_head (key : Int) (entries : List (Int × List Value)) :
    ((entries.dropWhile fun entry => entry.1 != key).head?).map Prod.snd =
      BTree.Abstract.lookupList key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, row⟩
    by_cases same : other = key
    · simp [List.dropWhile, BTree.Abstract.lookupList, same]
    · have skip : (other != key) = true := by simpa using same
      simpa [List.dropWhile, BTree.Abstract.lookupList, same, skip] using ih

theorem observe_pointProgram {db : Database} {database root column : Nat} {table : Table}
    (found : db database root = some table) (key : Int64) :
    observe (run db (pointProgram database root column key) 6 initial) =
      ⟨((table.get key.toInt).map fun row => [row[column]?.getD .null]).toList, .halted 0⟩ := by
  rw [table.get_eq, ← seek_head]
  cases dropped : table.entries.dropWhile (fun entry => entry.1 != key.toInt) <;>
    simp [pointProgram, initial, Vdbe.run, Vdbe.step, Vdbe.execute, found, Vdbe.State.initial,
      Vdbe.State.advance, Vdbe.State.write, Vdbe.State.setCursor, Vdbe.State.seekCursor,
      Vdbe.State.jump, Vdbe.Cursor.current?, Vdbe.State.emit, dropped, observe]

theorem pointProgram_lookup {db : Database} {database root column : Nat} {table : Table}
    (found : db database root = some table) (key : Int64) :
    pointResult (observe (run db (pointProgram database root column key) 6 initial)) =
      .ok ((table.get key.toInt).map fun row => row[column]?.getD .null) := by
  rw [observe_pointProgram found]
  cases table.get key.toInt <;> rfl

end Silmaril.Proofs.Machine.SQLite.VirtualMachine
