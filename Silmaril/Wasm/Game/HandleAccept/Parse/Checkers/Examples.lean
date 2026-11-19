module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Checkers.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Parse.Replay

/-!
# Executable one-shot parsers: examples (non-vacuity)

`nzParse_sound` (`Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers.Thms`) bounds the input/tree
relation of `nzParse` by the single nonzero words. Here it is shown non-empty by running the
module: the call `parse(7)` (candidate argument `7`) is replayed on the verified interpreter,
**including its export answer** (`Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.replayExportR`),
with a host whose `word` returns the handle `1` (`wordScript`), by kernel evaluation; the export
answers `1`, so `([7], x)` is related for any tree `x` that handle `1` denotes
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.mem_parseRel_of_replay`).

**Profiles and policies.** Every profile `P` admitting the deterministic steps of the interpreter
(hypothesis `hP`; every specification profile `Profile.spec nd {}`, the `_spec` corollaries),
and every parsing policy whose sentinel is not `1` (hypothesis `hs`; in particular the sentinel
`0` of `nzParse_sound`).

* `oneEnv x`: handle `1` denotes `x`; no other handle is defined.
* `([7], x)` is in the relation of `nzParse`, for every tree type and tree `x`
  (`nzParse_relates_7`); `[7]` is in its input language (`nzParse_input_7`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Accept.Handle Silmaril.Accept.Parse

/-- The host of `nzParse`: `word` returns the handle `1`. -/
def wordScript : Script := fun _ _ _ => [Val.i32 1]

/-- Handle `1` denotes `x`; no other handle is defined. -/
def oneEnv {X : Type} (x : X) : Silmaril.Accept.Handle.Env (BitVec 32) X := fun h =>
  if h = 1 then some x else none

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : PPolicy (BitVec 32)} (hs : pol.sentinel ≠ 1)
include hP hs

open Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing (mem_parseRel_of_replay)

theorem nzParse_relates_7 {X : Type} (x : X) :
    ([7], x) ∈ moduleParseRel P nzParse nzIx pol {oneEnv x} :=
  mem_parseRel_of_replay nzParse_instance hP nzIx pol (Set.mem_singleton _)
    (good := fun h => decide (h = 1))
    (fun h hh => by
      cases of_decide_eq_true hh
      exact ⟨fun e => hs e.symm, by simp [oneEnv]⟩)
    wordScript refFuel 4 ⟨0, by decide +kernel⟩ 7 7 1 (by simp [oneEnv])
    (by decide +kernel) (by decide +kernel)

theorem nzParse_input_7 {X : Type} (x : X) :
    [7] ∈ inputLang (moduleParseRel P nzParse nzIx pol {oneEnv x}) :=
  ⟨_, nzParse_relates_7 hP hs x, rfl⟩

end Positive

/-! ### At the specification profiles -/

theorem nzParse_relates_7_spec (nd : Bool) {pol : PPolicy (BitVec 32)} (hs : pol.sentinel ≠ 1)
    {X : Type} (x : X) :
    ([7], x) ∈ moduleParseRel (Profile.spec nd {}) nzParse nzIx pol {oneEnv x} :=
  nzParse_relates_7 (fun _ _ h => Step.deterministic_refines_spec nd h) hs x

theorem nzParse_input_7_spec (nd : Bool) {pol : PPolicy (BitVec 32)} (hs : pol.sentinel ≠ 1)
    {X : Type} (x : X) :
    [7] ∈ inputLang (moduleParseRel (Profile.spec nd {}) nzParse nzIx pol {oneEnv x}) :=
  nzParse_input_7 (fun _ _ h => Step.deterministic_refines_spec nd h) hs x

end Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers
