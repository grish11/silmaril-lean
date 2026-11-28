module

public import Silmaril.Formats.Sqlite.Vdbe.Defs

/-! Fixed-code SQLite bytecode over a supplied snapshot of rowid tables.
The opcode reference is SQLite 3.54.1, https://www.sqlite.org/opcode.html,
at Fossil check-in
`555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
The matching split source is
https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c.
The view omits prepared-statement bookkeeping, transaction setup, callbacks,
and the storage operations behind cursor creation. The caller supplies the
table snapshot and an already bound signed 64-bit key.
-/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine

open Silmaril.Formats.Sqlite

abbrev Instruction := Vdbe.Instruction
abbrev Program := Vdbe.Program
abbrev Table := Vdbe.Table
abbrev Database := Vdbe.Database
abbrev State := Vdbe.State
abbrev Fault := Vdbe.Error
abbrev RunResult := Vdbe.RunResult

def initial : State := Vdbe.State.initial

abbrev step : Database → Program → State → Except Fault State := Vdbe.step

abbrev run : Database → Program → Nat → State → RunResult := Vdbe.run

/-- Zero-based column and instruction addresses. The bound key is an Int64
immediate. A missed seek jumps directly to the successful halt. -/
def pointProgram (database root column : Nat) (key : Int64) : Program :=
  #[.openRead 0 root database, .int64 key 1, .seekRowid 0 5 1,
    .column 0 column 2, .resultRow 2 1, .halt 0]

abbrev RawInstruction := Vdbe.RawInstruction

/-- Lower one named instruction in the point-query profile. P1–P3 must fit
signed 32-bit slots and P5 is zero. The operand rules are:

* Init: fresh P1, no corruption target or trace payload.
* Goto: unused P1/P3 zero, no P4.
* Integer / Int64: signed P1 or split low P1/high P3, positive P2, no P4.
* OpenRead: immediate positive root, nonnegative DB and cursor, positive
  P4_INT32 table field count. The count is erased. The caller must supply a
  matching rowid table and ensure that Column operands fit the cursor's width.
* SeekRowid: nonzero miss target, positive key register, no P4. Execution
  requires an integer key.
* Column: zero-based column and no P4 default value or P5 shortcuts.
* ResultRow: positive first register and positive count, unused P3 zero.
* Halt: successful top-level halt with zero operands and no P4.

The result validates operand forms. Code addresses, register/cursor bounds,
cursor positioning, result arity and whole-program invariants are separate
conditions. Numeric or number/name opcodes, pointers and other names or flag
combinations are rejected. -/
def decodePoint? (raw : RawInstruction) : Option Instruction := do
  let .name name := raw.opcode | none
  if !(Vdbe.signed32 raw.p1 && Vdbe.signed32 raw.p2 && Vdbe.signed32 raw.p3) then none
  else
    let allowed : Bool := match name with
      | "Init" | "Int64" | "Column" => raw.p4 == .none
      | "Goto" => raw.p1 == 0 && raw.p3 == 0
      | "Integer" => raw.p3 == 0
      | "OpenRead" => match raw.p4 with
        | .integer width => Vdbe.signed32 width && decide (0 < width)
        | _ => false
      | "SeekRowid" => decide (0 < raw.p2)
      | "ResultRow" => raw.p3 == 0 && decide (0 < raw.p2)
      | "Halt" => raw.p1 == 0
      | _ => false
    if allowed then Vdbe.decode? raw else none

inductive Termination where
  | halted (code : Nat)
  | exhausted
  | fault (reason : Fault)
  /-- A manually constructed halted result with no halt code in its state. -/
  | missingHaltCode
  deriving DecidableEq

/-- Rows in emission order, including rows emitted before exhaustion or fault. -/
structure Observation where
  rows : List (List Value)
  termination : Termination
  deriving DecidableEq

def observe : RunResult → Observation
  | .halted state =>
      ⟨state.rows, match state.halted with
        | some code => .halted code
        | none => .missingHaltCode⟩
  | .exhausted state => ⟨state.rows, .exhausted⟩
  | .fault reason state => ⟨state.rows, .fault reason⟩

inductive PointError where
  | termination (status : Termination)
  | rowShape
  deriving DecidableEq

/-- A single SQL NULL cell is `ok (some .null)`. Only no rows yields
`ok none`. -/
def pointResult (obs : Observation) : Except PointError (Option Value) :=
  match obs.termination with
  | .halted 0 =>
      match obs.rows with
      | [] => .ok none
      | [[value]] => .ok (some value)
      | _ => .error .rowShape
  | status => .error (.termination status)

end Silmaril.Machine.SQLite.VirtualMachine
