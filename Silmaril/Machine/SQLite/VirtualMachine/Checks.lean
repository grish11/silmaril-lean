module

import Silmaril.Machine.SQLite.VirtualMachine.Thms

namespace Silmaril.Machine.SQLite.VirtualMachine

open Silmaril.Formats.Sqlite

example : decodePoint? { opcode := .name "Int64", p1 := -1, p2 := 1, p3 := -1 } =
    some (.int64 (-1) 1) := by decide

example : decodePoint? { opcode := .name "OpenRead", p2 := 2, p4 := .integer 2 } =
    some (.openRead 0 2 0) := by decide

example : decodePoint? { opcode := .name "OpenRead", p2 := 2, p4 := .integer 2, p5 := 2 } =
    none := by decide

example : decodePoint? { opcode := .name "SeekRowid", p3 := 1 } = none := by decide

example : decodePoint? { opcode := .name "Column", p3 := 1, p4 := .integer 7 } =
    none := by decide

example : decodePoint? { opcode := .name "Variable", p1 := 1, p2 := 1 } = none := by decide

example : pointResult ⟨[[.null]], .halted 0⟩ = .ok (some .null) := rfl
example : pointResult ⟨[], .halted 0⟩ = .ok none := rfl

example : observe (run (fun _ _ => none) #[.goto 0] 2 initial) = ⟨[], .exhausted⟩ := rfl

example : observe (run (fun _ _ => none) #[.goto 1] 2 initial) =
    ⟨[], .fault (.programCounter 1)⟩ := rfl

end Silmaril.Machine.SQLite.VirtualMachine
