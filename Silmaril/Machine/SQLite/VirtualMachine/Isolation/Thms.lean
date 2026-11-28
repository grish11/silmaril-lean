module

public import Silmaril.Machine.SQLite.VirtualMachine.Isolation.Defs
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Isolation

/-! Public universal prefix-safety theorems for the high-level read-only SQLite
VDBE VM.

The top-level theorems (`profileTrace_safe`, `runProfile_safe`,
`runProfile_no_bad_effects`) quantify over **all** representable raw VDBE
programs (`raw : Vdbe.RawProgram`), **all** `HostState` snapshots, and **all**
finite execution prefixes under a configured `Profile`—with **no** precondition
that the input program is valid, admitted, trusted, within a selected SQL
subset, or early-rejected.

- Intermediate per-step lemmas (`profileStep_safe`, `stepProfile_safe`) assume
  `StateInv` and show one step preserves `StateInv`, leaves `HostState`
  unchanged, and emits no `Effect.Bad`.
- Whole-input prefix theorems (`profileTrace_safe`, `runProfile_safe`,
  `runProfile_no_bad_effects`) establish `StateInv` from `initial` for every
  reachable execution prefix, independent of whether execution succeeds, errors,
  halts, or exhausts fuel (potentially diverging).
- In `ProfileStep`/`ProfileTrace`, handling of unmodeled or out-of-profile raw
  instructions is unconstrained except for `FallbackSafe`.

Explicit domain and outstanding gaps:
- Covers only high-level single-connection VDBE execution over `Vdbe.RawProgram`
  and immutable `Vdbe.Database` snapshots.
- Does NOT cover SQL parsing, preparation, or cleanup; does NOT prove
  confidentiality/noninterference, termination, blanket step/memory resource
  caps, query-result correctness, or C/ELF refinement/security of `libsqlite3.so`.
-/

public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Isolation

open Silmaril.Formats.Sqlite

theorem effect_isBad_iff (profile : Profile) (e : Effect) :
    e.isBad profile = true ↔ e.Bad profile :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.effect_isBad_iff profile e

theorem bad_writeTable (profile : Profile) (db root : Nat) :
    (Effect.writeTable db root).Bad profile :=
  trivial

theorem bad_attachDb (profile : Profile) (name : String) :
    (Effect.attachDb name).Bad profile :=
  trivial

theorem bad_loadExtension (profile : Profile) (path : String) :
    (Effect.loadExtension path).Bad profile :=
  trivial

theorem bad_hostEscape (profile : Profile) (op : String) :
    (Effect.hostEscape op).Bad profile :=
  trivial

theorem withinProfile_iff (profile : Profile) (instr : Instruction) :
    withinProfile profile instr = true ↔ InstructionInProfile profile instr :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.withinProfile_iff profile instr

theorem stateInv_initial (profile : Profile) (host : HostState) :
    StateInv profile host initial :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.stateInv_initial profile host

theorem execute_preserves_stateInv {profile : Profile} {host : HostState}
    {instr : Instruction} {s s' : State}
    (hprof : InstructionInProfile profile instr)
    (hinv : StateInv profile host s)
    (hexec : Vdbe.execute host.databases instr s = .ok s') :
    StateInv profile host s' :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.execute_preserves_stateInv hprof hinv hexec

theorem modeledEffects_not_bad {profile : Profile} {instr : Instruction}
    (hprof : InstructionInProfile profile instr) (s : State) (outcome : Except Fault State) :
    ∀ e ∈ modeledEffects instr s outcome, ¬ e.Bad profile :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.modeledEffects_not_bad hprof s outcome

/-- Intermediate per-step safety lemma for `ProfileStep`: assuming `StateInv`
and `FallbackSafe`, one step of any raw program emits no bad host effects,
leaves `HostState` unchanged, and preserves `StateInv`. -/
theorem profileStep_safe {profile : Profile} {fallback : Fallback}
    (hsafe : FallbackSafe profile fallback) {raw : Vdbe.RawProgram}
    {host host' : HostState} {s s' : State} {evs : List Effect}
    (hinv : StateInv profile host s)
    (hstep : ProfileStep profile fallback raw (host, s) evs (host', s')) :
    (∀ e ∈ evs, ¬ e.Bad profile) ∧ host' = host ∧ StateInv profile host' s' :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.profileStep_safe hsafe hinv hstep

/-- Whole-input finite-prefix safety for `ProfileTrace`: for **any** raw VDBE
program `raw`, **any** `HostState`, and **any** safety-preserving `fallback`,
every finite execution prefix from `(host, initial)` avoids `Effect.Bad`,
leaves `HostState` unchanged, and maintains `StateInv`. -/
theorem profileTrace_safe {profile : Profile} {fallback : Fallback}
    (hsafe : FallbackSafe profile fallback)
    (host : HostState) (raw : Vdbe.RawProgram)
    {evs : List Effect} {host' : HostState} {s' : State}
    (htrace : ProfileTrace profile fallback raw (host, initial) evs (host', s')) :
    (∀ e ∈ evs, ¬ e.Bad profile) ∧ host' = host ∧ StateInv profile host' s' :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.profileTrace_safe hsafe host raw htrace

/-- Intermediate per-step safety lemma for the concrete executable `stepProfile`. -/
theorem stepProfile_safe {profile : Profile} {host : HostState}
    (raw : Vdbe.RawProgram) {s : State} (hinv : StateInv profile host s) :
    (∀ e ∈ (stepProfile profile host raw s).1, ¬ e.Bad profile) ∧
    (∀ host' s', (stepProfile profile host raw s).2 = .ok (host', s') →
      host' = host ∧ StateInv profile host' s') :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.stepProfile_safe raw hinv

/-- Whole-input finite-prefix safety for the concrete executable `runProfile`:
for **any** raw VDBE program `raw`, **any** `HostState`, and **any** `fuel`,
the finite prefix avoids `Effect.Bad`, leaves `HostState` unchanged, and
maintains `StateInv` at the final state (whether halted, exhausted, or faulted). -/
theorem runProfile_safe (profile : Profile) (host : HostState)
    (raw : Vdbe.RawProgram) (fuel : Nat) :
    (∀ e ∈ (runProfile profile host raw fuel initial).events, ¬ e.Bad profile) ∧
    (runProfile profile host raw fuel initial).host = host ∧
    StateInv profile (runProfile profile host raw fuel initial).host
      (runProfile profile host raw fuel initial).result.state :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.runProfile_safe profile host raw fuel

/-- Explicit bad-event exclusion over all raw inputs and finite prefixes:
no `writeTable`, `attachDb`, `loadExtension`, or `hostEscape` occurs, every
`readTable` is authorized by `profile.canRead`, and every `emitRow` respects
`profile.maxResultWidth`. -/
theorem runProfile_no_bad_effects (profile : Profile) (host : HostState)
    (raw : Vdbe.RawProgram) (fuel : Nat) :
    ∀ e ∈ (runProfile profile host raw fuel initial).events,
      (∀ db root, e ≠ .writeTable db root) ∧
      (∀ name, e ≠ .attachDb name) ∧
      (∀ path, e ≠ .loadExtension path) ∧
      (∀ op, e ≠ .hostEscape op) ∧
      (∀ db root found, e = .readTable db root found → profile.canRead db root = true) ∧
      (∀ cells, e = .emitRow cells → cells.length ≤ profile.maxResultWidth) :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.runProfile_no_bad_effects profile host raw fuel

/-- Correspondence with `Vdbe.execute` on modeled in-profile instructions. -/
theorem stepProfile_eq_vm_execute {profile : Profile} {host : HostState}
    {raw : Vdbe.RawProgram} {s : State} {rawInstr : RawInstruction} {instr : Instruction}
    (hactive : s.halted = none)
    (hfetch : raw[s.pc]? = some rawInstr)
    (hdec : Vdbe.decode? rawInstr = some instr)
    (hwp : withinProfile profile instr = true) :
    (stepProfile profile host raw s).2 =
      match Vdbe.execute host.databases instr s with
      | .ok s' => .ok (host, s')
      | .error err => .error (.vm err) :=
  Proofs.Machine.SQLite.VirtualMachine.Isolation.stepProfile_eq_vm_execute hactive hfetch hdec hwp

end Silmaril.Machine.SQLite.VirtualMachine.Isolation
