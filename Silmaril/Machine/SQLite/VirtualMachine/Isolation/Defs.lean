module

public import Silmaril.Machine.SQLite.VirtualMachine.Defs

/-! High-level read-only profile safety model for the Silmaril SQLite VDBE VM.

This module extends Silmaril's existing read-only VDBE core
(`Silmaril.Formats.Sqlite.Vdbe.Defs` and `Silmaril.Machine.SQLite.VirtualMachine.Defs`)
to state and prove universal prefix safety over **all** representable raw VDBE
programs (`Vdbe.RawProgram`) under a configured read-only `Profile` and stated
host/fallback contracts—with **no** precondition that the input program is
valid, admitted, trusted, within a selected SQL subset, or early-rejected.

Model structure:
1. `Profile`: read-only capability and internal execution bounds (`canRead`,
   `maxRegisters`, `maxCursors`, `maxResultWidth`), enforced internally during
   execution rather than as input-filter premises.
2. `HostState` and `Effect` / `Effect.Bad`: explicit host state (`databases`,
   `attached`, `extensions`, `writeCount`) and effect alphabet containing both
   allowed read-only effects (`readTable`, `emitRow`) and bad mutation/escape
   effects (`writeTable`, `attachDb`, `loadExtension`, `hostEscape`,
   unauthorized `readTable`, over-width `emitRow`).
3. `ProfileStep` / `ProfileTrace`: small-step relational execution over arbitrary
   `Vdbe.RawProgram`, parameterized by an arbitrary `Fallback` relation for
   unmodeled or out-of-profile raw instructions whose behavior is unconstrained
   except for `FallbackSafe` (preserving absence of bad effects, `HostState`,
   and `StateInv`).
4. `stepProfile` / `runProfile`: concrete deterministic executable instance of
   the same profile over arbitrary `Vdbe.RawProgram` and finite step budgets
   `fuel : Nat`.

Explicit domain and outstanding gaps:
- Domain: single-connection, single-thread high-level VDBE execution over an
  immutable `Vdbe.Database` snapshot and arbitrary `Vdbe.RawProgram`.
- Does NOT cover SQL parsing, preparation, or cleanup; does NOT prove
  confidentiality/noninterference, termination, blanket step/memory resource
  caps, query-result correctness, or C/ELF refinement/security of `libsqlite3.so`.
- In `ProfileStep`, handling of unmodeled/out-of-profile opcodes relies on the
  stated `FallbackSafe` contract, which must be discharged when modeling
  additional opcodes or lowering to native code.
-/

@[expose] public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Isolation

open Silmaril.Formats.Sqlite

/-- Read-only host capability and internal execution-bound profile for a
single-connection SQLite VM execution. Limits are enforced internally during
execution, not assumed as input filters. -/
structure Profile where
  /-- Authorizes `(database, root)` pairs that `OpenRead` may access. -/
  canRead : Nat → Nat → Bool
  /-- Internal upper bound on register indices written by modeled opcodes (`1 ≤ r ≤ maxRegisters`). -/
  maxRegisters : Nat
  /-- Internal strict upper bound on cursor identifiers (`cursor < maxCursors`). -/
  maxCursors : Nat
  /-- Internal upper bound on the column width of any `ResultRow`. -/
  maxResultWidth : Nat

/-- Standard single-database read-only profile permitting reads only on `main`
(database id `0`) within the given internal register, cursor, and row-width
bounds. -/
def Profile.mainDbOnly (maxRegisters maxCursors maxResultWidth : Nat) : Profile where
  canRead := fun db _ => db == 0
  maxRegisters := maxRegisters
  maxCursors := maxCursors
  maxResultWidth := maxResultWidth

/-- Abstract host/environment state outside the VM's registers and cursors.
`databases` holds the protected read-only table snapshots; `attached`,
`extensions`, and `writeCount` model host surfaces that must remain unchanged
across every execution prefix under a read-only profile. -/
structure HostState where
  databases : Database
  attached : List String := []
  extensions : List String := []
  writeCount : Nat := 0

/-- Observable VM-to-host effect events. Both read-only effects and bad
mutation/attach/extension/escape effects are representable in this alphabet so
that bad-event exclusion theorems are non-tautological. -/
inductive Effect where
  | readTable (database root : Nat) (found : Bool)
  | emitRow (cells : List Value)
  | writeTable (database root : Nat)
  | attachDb (name : String)
  | loadExtension (path : String)
  | hostEscape (opcode : String)
  deriving DecidableEq

/-- Bad host events excluded by read-only profile safety: any write, attach,
extension load, host escape, unauthorized table read, or result row exceeding
the profile's width bound. -/
def Effect.Bad (profile : Profile) : Effect → Prop
  | .readTable db root _ => profile.canRead db root = false
  | .emitRow cells => profile.maxResultWidth < cells.length
  | .writeTable _ _ => True
  | .attachDb _ => True
  | .loadExtension _ => True
  | .hostEscape _ => True

/-- Decidable boolean check corresponding to `Effect.Bad`. -/
def Effect.isBad (profile : Profile) : Effect → Bool
  | .readTable db root _ => !(profile.canRead db root)
  | .emitRow cells => decide (profile.maxResultWidth < cells.length)
  | .writeTable _ _ => true
  | .attachDb _ => true
  | .loadExtension _ => true
  | .hostEscape _ => true

/-- Internal per-instruction profile guard checked during execution of a
modeled VDBE instruction. This is an internal execution mechanism, not a
precondition on raw inputs. -/
def InstructionInProfile (profile : Profile) : Instruction → Prop
  | .init _ | .goto _ | .halt _ => True
  | .integer _ destination | .int64 _ destination | .string8 _ destination =>
      1 ≤ destination ∧ destination ≤ profile.maxRegisters
  | .null _ _ => True
  | .copy _ destination additional =>
      1 ≤ destination ∧ destination + additional ≤ profile.maxRegisters
  | .openRead cursor root database =>
      profile.canRead database root = true ∧ cursor < profile.maxCursors
  | .rewind cursor _ | .next cursor _ =>
      cursor < profile.maxCursors
  | .column cursor _ destination | .rowid cursor destination =>
      cursor < profile.maxCursors ∧ 1 ≤ destination ∧ destination ≤ profile.maxRegisters
  | .resultRow _ count =>
      count ≤ profile.maxResultWidth
  | .seekRowid cursor _ _ =>
      cursor < profile.maxCursors

/-- Executable internal profile guard corresponding to `InstructionInProfile`. -/
def withinProfile (profile : Profile) : Instruction → Bool
  | .init _ | .goto _ | .halt _ => true
  | .integer _ destination | .int64 _ destination | .string8 _ destination =>
      decide (1 ≤ destination ∧ destination ≤ profile.maxRegisters)
  | .null _ _ => true
  | .copy _ destination additional =>
      decide (1 ≤ destination ∧ destination + additional ≤ profile.maxRegisters)
  | .openRead cursor root database =>
      profile.canRead database root && decide (cursor < profile.maxCursors)
  | .rewind cursor _ | .next cursor _ =>
      decide (cursor < profile.maxCursors)
  | .column cursor _ destination | .rowid cursor destination =>
      decide (cursor < profile.maxCursors ∧ 1 ≤ destination ∧ destination ≤ profile.maxRegisters)
  | .resultRow _ count =>
      decide (count ≤ profile.maxResultWidth)
  | .seekRowid cursor _ _ =>
      decide (cursor < profile.maxCursors)

/-- Per-state isolation and confinement invariant for a VM state relative to
`profile` and `host`. Established from `initial` for every reachable execution
over any raw input. -/
structure StateInv (profile : Profile) (host : HostState) (s : State) : Prop where
  /-- Every non-null register lies within `[1, profile.maxRegisters]`. -/
  registersConfined : ∀ r, s.registers r ≠ .null → 1 ≤ r ∧ r ≤ profile.maxRegisters
  /-- Every open cursor has an in-bounds identifier and provenance from an
  authorized `(database, root)` entry in `host.databases`. -/
  cursorsConfined : ∀ cid cursor, s.cursors cid = some cursor →
    cid < profile.maxCursors ∧
    ∃ db root, profile.canRead db root = true ∧ host.databases db root = some cursor.table
  /-- Every emitted row respects the profile's result width bound. -/
  rowsBounded : ∀ row ∈ s.rows, row.length ≤ profile.maxResultWidth

/-- Effects emitted by one modeled in-profile VDBE instruction step. -/
def modeledEffects (instr : Instruction) (s : State) (outcome : Except Fault State) :
    List Effect :=
  match instr, outcome with
  | .openRead _ root database, .ok _ => [.readTable database root true]
  | .openRead _ root database, .error _ => [.readTable database root false]
  | .resultRow first count, .ok _ =>
      [.emitRow ((List.range count).map fun offset => s.registers (first + offset))]
  | _, _ => []

/-- Transition relation for raw instructions outside the modeled in-profile
VDBE core (unmodeled opcodes, mutating opcodes, or out-of-profile operands).
Unconstrained except for `FallbackSafe`. -/
abbrev Fallback := RawInstruction → HostState × State → List Effect → HostState × State → Prop

/-- Safety contract on fallback handling of unmodeled or out-of-profile raw
instructions: handling may halt, error, no-op, or take any internal transition,
provided it emits no bad host effects, leaves `HostState` unchanged, and
preserves `StateInv`. -/
def FallbackSafe (profile : Profile) (fallback : Fallback) : Prop :=
  ∀ rawInstr host s evs host' s',
    StateInv profile host s →
    fallback rawInstr (host, s) evs (host', s') →
    (∀ e ∈ evs, ¬ e.Bad profile) ∧
    host' = host ∧
    StateInv profile host' s'

/-- Small-step relational execution of an arbitrary raw VDBE program under
`profile` and a `fallback` handler for unmodeled/out-of-profile instructions.
No input validity or admission assumption is placed on `raw`. -/
inductive ProfileStep (profile : Profile) (fallback : Fallback) (raw : Vdbe.RawProgram) :
    HostState × State → List Effect → HostState × State → Prop where
  | modeledOk {host s rawInstr instr s'}
      (active : s.halted = none)
      (fetch : raw[s.pc]? = some rawInstr)
      (decoded : Vdbe.decode? rawInstr = some instr)
      (inProfile : withinProfile profile instr = true)
      (exec : Vdbe.execute host.databases instr s = .ok s') :
      ProfileStep profile fallback raw (host, s)
        (modeledEffects instr s (.ok s')) (host, s')
  | modeledFault {host s rawInstr instr err}
      (active : s.halted = none)
      (fetch : raw[s.pc]? = some rawInstr)
      (decoded : Vdbe.decode? rawInstr = some instr)
      (inProfile : withinProfile profile instr = true)
      (exec : Vdbe.execute host.databases instr s = .error err)
      (code : Nat) :
      ProfileStep profile fallback raw (host, s)
        (modeledEffects instr s (.error err)) (host, {s with halted := some code})
  | fallbackStep {host s rawInstr evs host' s'}
      (active : s.halted = none)
      (fetch : raw[s.pc]? = some rawInstr)
      (outside : match Vdbe.decode? rawInstr with
        | some instr => withinProfile profile instr = false
        | none => true)
      (step : fallback rawInstr (host, s) evs (host', s')) :
      ProfileStep profile fallback raw (host, s) evs (host', s')

/-- Finite execution prefix of arbitrary length over `ProfileStep`. -/
inductive ProfileTrace (profile : Profile) (fallback : Fallback) (raw : Vdbe.RawProgram) :
    HostState × State → List Effect → HostState × State → Prop where
  | nil (cfg) : ProfileTrace profile fallback raw cfg [] cfg
  | cons {cfg1 cfg2 cfg3 evs1 evs2} :
      ProfileStep profile fallback raw cfg1 evs1 cfg2 →
      ProfileTrace profile fallback raw cfg2 evs2 cfg3 →
      ProfileTrace profile fallback raw cfg1 (evs1 ++ evs2) cfg3

/-- Runtime fault of the concrete executable profile runner. -/
inductive ProfileFault where
  | vm (fault : Fault)
  | outsideProfile (raw : RawInstruction)
  deriving DecidableEq

/-- Result of a finite-prefix run of the concrete executable profile runner. -/
inductive ProfileRunResult where
  | halted (state : State)
  | exhausted (state : State)
  | fault (reason : ProfileFault) (state : State)

def ProfileRunResult.state : ProfileRunResult → State
  | .halted s | .exhausted s | .fault _ s => s

/-- Concrete executable single step over an arbitrary `Vdbe.RawProgram` under
`profile`. -/
def stepProfile (profile : Profile) (host : HostState) (raw : Vdbe.RawProgram) (s : State) :
    List Effect × Except ProfileFault (HostState × State) :=
  if s.halted.isSome then ([], .error (.vm .alreadyHalted)) else
    match raw[s.pc]? with
    | none => ([], .error (.vm (.programCounter s.pc)))
    | some rawInstr =>
        match Vdbe.decode? rawInstr with
        | some instr =>
            if withinProfile profile instr then
              let next := Vdbe.execute host.databases instr s
              (modeledEffects instr s next,
                match next with
                | .ok s' => .ok (host, s')
                | .error err => .error (.vm err))
            else
              ([], .error (.outsideProfile rawInstr))
        | none =>
            ([], .error (.outsideProfile rawInstr))

/-- Output of a finite-prefix execution of `runProfile`. -/
structure ProfileOutcome where
  events : List Effect
  host : HostState
  result : ProfileRunResult

/-- Concrete executable finite-prefix runner over an arbitrary `Vdbe.RawProgram`
for `fuel : Nat` steps under `profile`. -/
def runProfile (profile : Profile) (host : HostState) (raw : Vdbe.RawProgram) :
    Nat → State → ProfileOutcome
  | fuel, s =>
      if s.halted.isSome then ⟨[], host, .halted s⟩ else
        match fuel with
        | 0 => ⟨[], host, .exhausted s⟩
        | fuel + 1 =>
          let (events, next) := stepProfile profile host raw s
          match next with
          | .error fault => ⟨events, host, .fault fault s⟩
          | .ok (host', after) =>
            let rest := runProfile profile host' raw fuel after
            ⟨events ++ rest.events, rest.host, rest.result⟩

/-- Potential host effect of an unguarded raw instruction (without profile
enforcement), used in `Checks` to witness that bad effects are genuinely
reachable in an unguarded model. -/
def unguardedRawEffect (raw : RawInstruction) : Option Effect :=
  match raw.opcode.name? with
  | some "OpenWrite" | some "Insert" | some "InsertInt" | some "Delete" =>
      some (.writeTable raw.p3.toNat raw.p2.toNat)
  | some "Attach" =>
      some (.attachDb (match raw.p4 with | .text s => s | _ => ""))
  | some "LoadExtension" =>
      some (.loadExtension (match raw.p4 with | .text s => s | _ => ""))
  | some "OpenRead" =>
      some (.readTable raw.p3.toNat raw.p2.toNat true)
  | some _ => none
  | none => some (.hostEscape "<numeric>")

end Silmaril.Machine.SQLite.VirtualMachine.Isolation
