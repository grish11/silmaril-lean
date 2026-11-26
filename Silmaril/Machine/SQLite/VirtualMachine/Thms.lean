module

public import Silmaril.Machine.SQLite.VirtualMachine.Defs
public import Silmaril.Formats.Sqlite.Vdbe.Thms
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Point

public section

namespace Silmaril.Machine.SQLite.VirtualMachine

open Silmaril.Formats.Sqlite

theorem step_iff {database program before after} :
    step database program before = .ok after ↔ Vdbe.Step database program before after :=
  Vdbe.step_iff

theorem run_trace (database : Database) (program : Program) (fuel : Nat) (before : State) :
    Vdbe.Trace database program before (run database program fuel before).state :=
  Vdbe.run_trace database program fuel before

/-- From the initial machine, the snapshot lookup determines the full ordered
row observation and the successful halt. -/
theorem observe_pointProgram {db : Database} {database root column : Nat} {table : Table}
    (found : db database root = some table) (key : Int64) :
    observe (run db (pointProgram database root column key) 6 initial) =
      ⟨((table.get key.toInt).map fun row => [row[column]?.getD .null]).toList, .halted 0⟩ :=
  Proofs.Machine.SQLite.VirtualMachine.observe_pointProgram found key

theorem pointProgram_lookup {db : Database} {database root column : Nat} {table : Table}
    (found : db database root = some table) (key : Int64) :
    pointResult (observe (run db (pointProgram database root column key) 6 initial)) =
      .ok ((table.get key.toInt).map fun row => row[column]?.getD .null) :=
  Proofs.Machine.SQLite.VirtualMachine.pointProgram_lookup found key

end Silmaril.Machine.SQLite.VirtualMachine
