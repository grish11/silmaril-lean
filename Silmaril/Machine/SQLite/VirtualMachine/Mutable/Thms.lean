module

public import Silmaril.Machine.SQLite.VirtualMachine.Mutable.Defs
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Mutable

public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Mutable

theorem ofProgram_represents (code : Program) (state : State) :
    Represents (Configuration.ofProgram code state) code state :=
  Proofs.Machine.SQLite.VirtualMachine.Mutable.ofProgram_represents code state

theorem step_state (db : Database) (cfg : Configuration) :
    (Mutable.step db cfg).map Configuration.state =
      VirtualMachine.step db cfg.erased cfg.state :=
  Proofs.Machine.SQLite.VirtualMachine.Mutable.step_state db cfg

theorem step_erased {db : Database} {before after : Configuration}
    (stepped : Mutable.step db before = .ok after) : after.erased = before.erased :=
  Proofs.Machine.SQLite.VirtualMachine.Mutable.step_erased stepped

/-- Full VM state, result category and fault reason agree for the same input
and fuel. The rewritten code continues to represent the original fixed code. -/
theorem run_represents (db : Database) (fuel : Nat) (cfg : Configuration) :
    (Mutable.run db fuel cfg).result = VirtualMachine.run db cfg.erased fuel cfg.state ∧
      (Mutable.run db fuel cfg).code.map Cell.erase = cfg.erased :=
  Proofs.Machine.SQLite.VirtualMachine.Mutable.run_represents db fuel cfg

end Silmaril.Machine.SQLite.VirtualMachine.Mutable
