module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Replay

/-!
# Executable cons writer builders: examples (non-vacuity)

`twoWords_sound` (`Silmaril.Wasm.Game.HandleAccept.Writers.Builders.Thms`) bounds the writer
language of `twoWords` by the lists `(x x+1)`. Here it is shown non-empty by running the module:
the call `run(k)` (candidate argument `k`, `Silmaril.Wasm.Resource.replayExport`) is replayed on
the verified interpreter with a host returning the fresh handles `1, 2, 3, …` (`freshScript`),
by kernel evaluation, and the writer host (store semantics, `WStep.writeOk` and
`WStep.acceptOk` steps) is simulated along the decoded writes and accept
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.mem_consWLang_of_replay`).

**Profiles and policies.** Every profile `P` admitting the deterministic steps of the
interpreter (hypothesis `hP`; every specification profile `Profile.spec nd {}`, the `_spec`
corollaries), and every writer policy whose sentinel, if any, is `0` (hypothesis `hs`; interning
and invalid-use policies are not exercised).

* `(0 1)` and `(5 6)` are in the writer language of `twoWords` (`twoWords_accepts_0`,
  `twoWords_accepts_5`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Writers.Builders

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle

/-- The host of `twoIx`: the `k`-th callout returns the fresh handle `k + 1`, except `accept`,
which returns nothing. -/
def freshScript : Script := fun k h _ =>
  if h = twoIx.accept then [] else [Val.i32 (BitVec.ofNat 32 (k + 1))]

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
  {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
include hP hs

open Silmaril.Proofs.Wasm.Game.HandleAccept.Writers (mem_consWLang_of_replay)

theorem twoWords_accepts_0 : SExp2.ofAtoms [0, 1] ∈ moduleConsWLang P twoWords twoIx pol :=
  mem_consWLang_of_replay twoWords_instance hP twoIx (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs r h]) freshScript refFuel 8 ⟨0, by decide +kernel⟩ 0
    (by decide +kernel)

theorem twoWords_accepts_5 : SExp2.ofAtoms [5, 6] ∈ moduleConsWLang P twoWords twoIx pol :=
  mem_consWLang_of_replay twoWords_instance hP twoIx (bad := fun r => decide (r = 0))
    (fun r h => by simp [hs r h]) freshScript refFuel 8 ⟨0, by decide +kernel⟩ 5
    (by decide +kernel)

end Positive

/-! ### At the specification profiles -/

theorem twoWords_accepts_0_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) :
    SExp2.ofAtoms [0, 1] ∈ moduleConsWLang (Profile.spec nd {}) twoWords twoIx pol :=
  twoWords_accepts_0 (fun _ _ h => Step.deterministic_refines_spec nd h) hs

theorem twoWords_accepts_5_spec (nd : Bool) {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) :
    SExp2.ofAtoms [5, 6] ∈ moduleConsWLang (Profile.spec nd {}) twoWords twoIx pol :=
  twoWords_accepts_5 (fun _ _ h => Step.deterministic_refines_spec nd h) hs

end Silmaril.Wasm.Game.HandleAccept.Writers.Builders
