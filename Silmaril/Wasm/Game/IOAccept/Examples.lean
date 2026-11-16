module

public import Silmaril.Wasm.Game.IOAccept.Thms
public import Silmaril.Wasm.Game.IOAccept.Example.Defs
import Silmaril.Proofs.Wasm.Game.IOAccept.Example

/-! # Traced I/O acceptance of core Wasm modules: examples and tests

* **A concrete module**: `exStart` (`Silmaril.Wasm.Game.Examples`) calls its import
  `"env" "f"` from its start function, and again when its export `"run"` (address `1`) is
  invoked. Against `unitEnv` (answers `values []`; satisfies the host contract), its traced
  session has the tags `runTags = [out f, enter 1, out f]` (`run_tsession`), for every profile.
  `bracket` drops the instantiation-phase call and keeps the invocation's
  (`bracket_runTags`), so `"run"` triggers exactly one call of `"env" "f"` in this trace, and
  `(1, ("env", "f")) ∈ triggers (entryIORuns P UEnvOk 0 exStart runRoles)` (`run_triggers`);
  the triggered call is a reachable callout (`run_callout`).
* **Tag-level tests**, by kernel evaluation: inputs and outputs before the first `enter` are
  outside every scope; a host answer read as an input (`answerIn`) starts a window of the
  invocation's later outputs; a trap ends a run with result `none`.

Proofs: `Silmaril.Proofs.Wasm.Game.IOAccept.Example`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.IOAccept.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Accept.IO Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Game.IOAccept.Example
  Silmaril.Wasm.Game.Examples

/-! ## A concrete module -/

/-- **The traced session of `exStart`**: the start function's call, the invocation of
`"run"`, and its call. -/
theorem run_tsession (P : Profile) : ∃ x, TSession P unitEnv exStart exC₀.frame.module.mems[0]?
    runRoles exC₀ () exI.addrs .run true x runTags :=
  Silmaril.Proofs.Wasm.Game.IOAccept.Example.run_tsession

/-- The start function's call is outside every scope; the invocation's call is in scope `1`
(the position of its `enter`). -/
theorem bracket_runTags : bracket runTags = [.enter 1 (some 1), .out 1 ("env", "f")] := by
  decide +kernel

/-- One entry run: `"run"` outputs one call of `"env" "f"`, and has not returned. -/
example : entryRuns (bracket runTags) = [⟨1, [("env", "f")], none⟩] := by decide +kernel

/-- **`"run"` triggers its call of `"env" "f"`**, for every profile. -/
theorem run_triggers (P : Profile) :
    (1, ("env", "f")) ∈ triggers (entryIORuns P UEnvOk 0 exStart runRoles) :=
  Silmaril.Proofs.Wasm.Game.IOAccept.Example.run_triggers

/-- The triggered output is a reachable callout of `exStart`. -/
theorem run_callout (P : Profile) :
    ∃ o ∈ Callouts P UEnvOk 0 exStart, o.imp = ("env", "f") :=
  let ⟨_, hr, _, hb⟩ := run_triggers P
  let ⟨o, ho, h⟩ := exists_callout_of_mem_entryIORuns hr hb
  ⟨o, ho, Option.some.inj h⟩

/-! ## Tag-level tests -/

/-- Tags of a session: `X = Nat` export addresses, inputs and outputs `Nat`, results `Nat`. -/
abbrev T := Tag Nat Nat Nat Nat

/-- An input and an output of the instantiation phase trigger nothing; the invocation's
answer-input `1` triggers its later outputs `2, 3`, and the invocation returns `0`. -/
example : inputRuns (bracket ([.inp 7, .out 8, .enter (some 4), .inp 1, .out 2, .out 3,
    .exit (some 0)] : List T)) = [⟨1, [2, 3], some 0⟩] := by decide +kernel

/-- The entry reading of the same trace: export `4` outputs `2, 3` and returns `0`. -/
example : entryRuns (bracket ([.inp 7, .out 8, .enter (some 4), .inp 1, .out 2, .out 3,
    .exit (some 0)] : List T)) = [⟨4, [2, 3], some 0⟩] := by decide +kernel

/-- Two invocations are two scopes: the second input does not trigger the first output; a trap
(`exit none`) ends the first run without a result. -/
example : inputRuns (bracket ([.enter none, .inp 1, .out 2, .exit none, .enter none, .inp 3,
    .out 4, .exit (some 5)] : List T)) = [⟨1, [2], none⟩, ⟨3, [4], some 5⟩] := by decide +kernel

/-- Flatness: a nested `enter` is not a traced session's shape. -/
example : openScan false ([.enter none, .enter none] : List T) = none := by decide

example : openScan false ([.out 1, .enter none, .exit none, .enter none] : List T) =
    some true := by decide

end Silmaril.Wasm.Game.IOAccept.Examples
