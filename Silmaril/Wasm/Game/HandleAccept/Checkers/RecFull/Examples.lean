module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecFull.Thms
public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Examples
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Replay

/-!
# The full recursive-properness checker: examples (non-vacuity)

As for the other checkers, the call `check(0)` is replayed on the verified interpreter with the
import answers of a concrete handle table, by kernel evaluation, and every decoded read is
checked correct in a concrete environment, handle `0` being accepted
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.mem_consLang_of_replay`). The replay runs the
recursion: `check(0)` calls `check(1)`, which calls `check(3)`; each accepts its argument.

* `deep1 = (((1)))` is accepted (`recFullCheck_accepts_deep1`, environment `deepEnv`: handle `0`
  the whole list, `1` the element `((1))`, `2` nil, `3` the element `(1)`, `4` the atom `1`),
  while no run of `recProperCheck` accepts it (`Thms.recProperCheck_rejects_deep1`);
* the nested list `nested123 = ((1 2) 3)` is accepted (`recFullCheck_accepts_nested`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle

/-- The handles of `(((1)))`. -/
def deepTab (h : BitVec 32) : Cell :=
  if h = 0 then ⟨2, 1, 2, 0⟩ else if h = 1 then ⟨2, 3, 2, 0⟩ else if h = 3 then ⟨2, 4, 2, 0⟩
  else if h = 4 then ⟨1, 0, 0, 1⟩ else ⟨0, 0, 0, 0⟩

/-- The environment of `deepTab`: handle `0` denotes `deep1`. -/
def deepEnv : HEnv := fun h =>
  if h = 0 then some deep1 else if h = 1 then some (SExp2.ofList [SExp2.ofAtoms [1]])
  else if h = 2 then some .nil else if h = 3 then some (SExp2.ofAtoms [1])
  else if h = 4 then some (.atom 1) else none

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
include hP

open Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers (mem_consLang_of_replay)

theorem recFullCheck_accepts_deep1 :
    deep1 ∈ moduleConsLang P recFullCheck consIx .trap .callTrap {deepEnv} :=
  mem_consLang_of_replay recFullCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx deepTab) refFuel 80 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem recFullCheck_accepts_nested :
    nested123 ∈ moduleConsLang P recFullCheck consIx .trap .callTrap {nestEnv} :=
  mem_consLang_of_replay recFullCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx nestTab) refFuel 80 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Positive

theorem recFullCheck_accepts_deep1_spec (nd : Bool) :
    deep1 ∈ moduleConsLang (Profile.spec nd {}) recFullCheck consIx .trap .callTrap {deepEnv} :=
  recFullCheck_accepts_deep1 fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- **`recFullCheck` strictly extends `recProperCheck`** on `(((1)))`, at the specification
profiles. -/
theorem recFullCheck_separates_deep1 (nd : Bool) :
    deep1 ∈ moduleConsLang (Profile.spec nd {}) recFullCheck consIx .trap .callTrap {deepEnv} ∧
      deep1 ∉ moduleConsLang (Profile.spec nd {}) recProperCheck consIx .trap .callTrap
        {deepEnv} :=
  ⟨recFullCheck_accepts_deep1_spec nd, recProperCheck_rejects_deep1 _ (by decide) _⟩

end Silmaril.Wasm.Game.HandleAccept.Checkers
