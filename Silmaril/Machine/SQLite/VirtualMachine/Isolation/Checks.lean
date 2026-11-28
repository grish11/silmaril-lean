module

import Silmaril.Machine.SQLite.VirtualMachine.Isolation.Thms

/-! Non-vacuity checks, concrete execution examples (normal halt, divergence
prefix, runtime fault, non-refusing safe fallback, and unguarded bad-effect
counterexamples), and axiom guards for `VirtualMachine.Isolation`. -/

namespace Silmaril.Machine.SQLite.VirtualMachine.Isolation.Checks

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine
open Silmaril.Machine.SQLite.VirtualMachine.Isolation

private def sampleProfile : Profile := Profile.mainDbOnly 4 2 2

private def sampleTable : Table :=
  BTree.Query.ReadModel.ofList
    [(1, [.text "alice"]), (2, [.text "bob"])]

private def sampleHost : HostState where
  databases := fun db root =>
    if db = 0 ∧ root = 2 then some sampleTable else none

/-- Legitimate read-only table-scan program in raw VDBE form:
`OpenRead 0 2 0; Rewind 0 5; Column 0 0 1; ResultRow 1 1; Next 0 2; Halt 0`. -/
private def scanRawProgram : Vdbe.RawProgram :=
  #[ { opcode := .name "OpenRead", p1 := 0, p2 := 2, p3 := 0 },
     { opcode := .name "Rewind", p1 := 0, p2 := 5 },
     { opcode := .name "Column", p1 := 0, p2 := 0, p3 := 1 },
     { opcode := .name "ResultRow", p1 := 1, p2 := 1 },
     { opcode := .name "Next", p1 := 0, p2 := 2 },
     { opcode := .name "Halt", p1 := 0 } ]

/-- Positive non-vacuity: running the raw scan program directly under
`sampleProfile` reads table `(0, 2)`, emits both rows, halts with code 0, and
leaves `sampleHost` unchanged. -/
example :
    let out := runProfile sampleProfile sampleHost scanRawProgram 10 initial
    out.events = [.readTable 0 2 true, .emitRow [.text "alice"], .emitRow [.text "bob"]] ∧
    out.result.state.rows = [[.text "alice"], [.text "bob"]] ∧
    out.result.state.halted = some 0 ∧
    out.host = sampleHost := by
  simp [runProfile, stepProfile, scanRawProgram, sampleProfile, Profile.mainDbOnly,
    sampleHost, sampleTable, initial, Vdbe.State.initial, Vdbe.decode?, Vdbe.RawOpcode.name?,
    Vdbe.operand?, Vdbe.register?, withinProfile, Vdbe.execute, modeledEffects,
    Vdbe.State.setCursor, Vdbe.State.advance, Vdbe.State.rewindCursor, Vdbe.State.jump,
    Vdbe.State.write, Vdbe.State.emit, Vdbe.State.nextCursor, Vdbe.Cursor.current?,
    BTree.Query.ReadModel.ofList, ProfileRunResult.state]

/-- Orthogonality to divergence: a non-terminating loop (`Goto 0`) executes any
finite prefix cleanly with zero bad effects and unchanged host state. -/
private def loopRawProgram : Vdbe.RawProgram :=
  #[ { opcode := .name "Goto", p2 := 0 } ]

example :
    let out := runProfile sampleProfile sampleHost loopRawProgram 5 initial
    out.events = [] ∧ out.result.state.halted = none ∧ out.host.writeCount = 0 :=
  ⟨rfl, rfl, rfl⟩

/-- Runtime error on an authorized missing table emits only an allowed read
attempt and leaves `sampleHost` unchanged. -/
private def missingTableRaw : Vdbe.RawProgram :=
  #[ { opcode := .name "OpenRead", p1 := 0, p2 := 99, p3 := 0 },
     { opcode := .name "Halt", p1 := 0 } ]

example :
    let out := runProfile sampleProfile sampleHost missingTableRaw 4 initial
    out.events = [.readTable 0 99 false] ∧ out.host.writeCount = 0 :=
  ⟨rfl, rfl⟩

/-- Running arbitrary raw programs containing `OpenWrite`, `Attach`,
`LoadExtension`, unknown numeric opcodes, unauthorized DBs, or out-of-bounds
operands under `sampleProfile` emits no bad effects and leaves `sampleHost`
unchanged—with no pre-execution input filter. -/
private def openWriteInstr : RawInstruction :=
  { opcode := .name "OpenWrite", p1 := 0, p2 := 2, p3 := 0 }

private def attachInstr : RawInstruction :=
  { opcode := .name "Attach", p4 := .text "other.db" }

private def loadExtInstr : RawInstruction :=
  { opcode := .name "LoadExtension", p4 := .text "ext.so" }

private def unknownNumericInstr : RawInstruction :=
  { opcode := .number 999 }

private def unauthorizedReadInstr : RawInstruction :=
  { opcode := .name "OpenRead", p1 := 0, p2 := 2, p3 := 1 }

example : (runProfile sampleProfile sampleHost #[openWriteInstr, { opcode := .name "Halt" }] 4 initial).events = [] := rfl
example : (runProfile sampleProfile sampleHost #[attachInstr] 4 initial).events = [] := rfl
example : (runProfile sampleProfile sampleHost #[loadExtInstr] 4 initial).events = [] := rfl
example : (runProfile sampleProfile sampleHost #[unknownNumericInstr] 4 initial).events = [] := rfl
example : (runProfile sampleProfile sampleHost #[unauthorizedReadInstr] 4 initial).events = [] := rfl
example : (runProfile sampleProfile sampleHost #[{ opcode := .name "Integer", p1 := 42, p2 := 5 }] 4 initial).events = [] := rfl
example : (runProfile sampleProfile sampleHost #[{ opcode := .name "OpenRead", p1 := 2, p2 := 2, p3 := 0 }] 4 initial).events = [] := rfl
example : (runProfile sampleProfile sampleHost #[{ opcode := .name "ResultRow", p1 := 1, p2 := 3 }] 4 initial).events = [] := rfl

/-- Non-refusing fallback example: a fallback that skips unmodeled opcodes via
`State.advance` (without refusing) still satisfies `FallbackSafe`, illustrating
that `profileTrace_safe` does not force refusal on unsupported opcodes. -/
private def skipFallback : Fallback :=
  fun _ cfg evs cfg' => evs = [] ∧ cfg' = (cfg.1, cfg.2.advance)

example (profile : Profile) : FallbackSafe profile skipFallback := by
  rintro _ host s evs host' s' hinv ⟨rfl, hcfg⟩
  cases hcfg
  exact ⟨(fun _ h => by cases h), rfl,
    ⟨hinv.registersConfined, hinv.cursorsConfined, hinv.rowsBounded⟩⟩

/-- Counterexamples without profile enforcement: `OpenWrite`, `Attach`,
`LoadExtension`, unknown numeric opcodes, and unauthorized `OpenRead` carry
`Effect.Bad` in an unguarded model. -/
example : ∃ e, unguardedRawEffect openWriteInstr = some e ∧ e.Bad sampleProfile :=
  ⟨.writeTable 0 2, rfl, bad_writeTable sampleProfile 0 2⟩

example : ∃ e, unguardedRawEffect attachInstr = some e ∧ e.Bad sampleProfile :=
  ⟨.attachDb "other.db", rfl, bad_attachDb sampleProfile "other.db"⟩

example : ∃ e, unguardedRawEffect loadExtInstr = some e ∧ e.Bad sampleProfile :=
  ⟨.loadExtension "ext.so", rfl, bad_loadExtension sampleProfile "ext.so"⟩

example : ∃ e, unguardedRawEffect unknownNumericInstr = some e ∧ e.Bad sampleProfile :=
  ⟨.hostEscape "<numeric>", rfl, bad_hostEscape sampleProfile "<numeric>"⟩

example : ∃ e, unguardedRawEffect unauthorizedReadInstr = some e ∧ e.Bad sampleProfile :=
  ⟨.readTable 1 2 true, rfl, rfl⟩

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.profileStep_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.profileStep_safe

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.profileTrace_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.profileTrace_safe

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.stepProfile_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.stepProfile_safe

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.runProfile_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.runProfile_safe

/--
info: 'Silmaril.Machine.SQLite.VirtualMachine.Isolation.runProfile_no_bad_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Machine.SQLite.VirtualMachine.Isolation.runProfile_no_bad_effects

end Silmaril.Machine.SQLite.VirtualMachine.Isolation.Checks
