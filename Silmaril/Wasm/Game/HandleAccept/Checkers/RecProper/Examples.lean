module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Thms
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Examples
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Replay

/-!
# The nested-list checker: examples (non-vacuity)

As for the other checkers (`Silmaril.Wasm.Game.HandleAccept.Checkers.Examples`), the call
`check(0)` is replayed on the verified interpreter with the import answers of a concrete handle
table (`cellScript`), by kernel evaluation, and every decoded read is checked correct in a
concrete environment, handle `0` being accepted
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.mem_consLang_of_replay`).

* `(1 2)` is accepted (`recProperCheck_accepts_12`, environment `listEnv 1 2`);
* the nested list `nested123 = ((1 2) 3)` is accepted (`recProperCheck_accepts_nested`,
  environment `nestEnv`: handle `0` the whole list, `1` the element `(1 2)`, `2` the atom `1`,
  `3` the tail `(2)`, `4` the atom `2`, `5` the outer tail `(3)`, `6` nil, `7` the atom `3`).
  `wordsCheck` accepts no run on it (`wordsCheck_rejects_nested`);
* `dottedElem = ((() . 1))` is accepted by `properCheck` (`properCheck_accepts_dottedElem`) and by
  no run of `recProperCheck` (`recProperCheck_rejects_dottedElem`, by soundness).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle

/-- The handles of `((1 2) 3)`. -/
def nestTab (h : BitVec 32) : Cell :=
  if h = 0 then ⟨2, 1, 5, 0⟩ else if h = 1 then ⟨2, 2, 3, 0⟩ else if h = 2 then ⟨1, 0, 0, 1⟩
  else if h = 3 then ⟨2, 4, 6, 0⟩ else if h = 4 then ⟨1, 0, 0, 2⟩
  else if h = 5 then ⟨2, 7, 6, 0⟩ else if h = 7 then ⟨1, 0, 0, 3⟩ else ⟨0, 0, 0, 0⟩

/-- The environment of `nestTab`: handle `0` denotes `nested123`. -/
def nestEnv : HEnv := fun h =>
  if h = 0 then some nested123 else if h = 1 then some (SExp2.ofAtoms [1, 2])
  else if h = 2 then some (.atom 1) else if h = 3 then some (SExp2.ofAtoms [2])
  else if h = 4 then some (.atom 2) else if h = 5 then some (SExp2.ofList [.atom 3])
  else if h = 6 then some .nil else if h = 7 then some (.atom 3) else none

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
include hP

open Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers (mem_consLang_of_replay)

theorem recProperCheck_accepts_12 :
    SExp2.ofAtoms [1, 2] ∈ moduleConsLang P recProperCheck consIx .trap .callTrap {listEnv 1 2} :=
  mem_consLang_of_replay recProperCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx (listTab 1 2)) refFuel 32 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem recProperCheck_accepts_nested :
    nested123 ∈ moduleConsLang P recProperCheck consIx .trap .callTrap {nestEnv} :=
  mem_consLang_of_replay recProperCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx nestTab) refFuel 40 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Positive

theorem recProperCheck_accepts_12_spec (nd : Bool) : SExp2.ofAtoms [1, 2] ∈
    moduleConsLang (Profile.spec nd {}) recProperCheck consIx .trap .callTrap {listEnv 1 2} :=
  recProperCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem recProperCheck_accepts_nested_spec (nd : Bool) : nested123 ∈
    moduleConsLang (Profile.spec nd {}) recProperCheck consIx .trap .callTrap {nestEnv} :=
  recProperCheck_accepts_nested fun _ _ hs => Step.deterministic_refines_spec nd hs

/-- `wordsCheck` accepts no run on the nested list. -/
theorem wordsCheck_rejects_nested (P : Profile) (Envs : Set HEnv) :
    nested123 ∉ moduleConsLang P wordsCheck consIx .trap .callTrap Envs :=
  fun h => nested123_not_mem_wordsL (wordsCheck_sound P (by decide) Envs h)

end Silmaril.Wasm.Game.HandleAccept.Checkers
