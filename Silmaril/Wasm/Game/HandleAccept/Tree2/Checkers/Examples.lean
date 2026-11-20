module

public import Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2.Replay

/-!
# Executable binary-tree reader checkers: examples (non-vacuity)

`combCheck_sound` (`Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers.Thms`) bounds the reader
language of `combCheck` by the right combs of words. Here it is shown non-empty by running the
module: the call `check(0)` (candidate argument `0`, `Silmaril.Wasm.Resource.replayExport`) is
replayed on the verified interpreter with the import answers of a concrete handle table
(`combScript`), by kernel evaluation, and every decoded read is checked correct in a concrete
environment, with handle `0` accepted
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2.mem_tree2Lang_of_replay`).

**Profiles.** Every profile `P` admitting the deterministic steps of the interpreter (hypothesis
`hP`), in particular every specification profile `Profile.spec nd {}` (the `_spec` corollary).

* `combEnv`: handle `0` denotes the comb `comb [1, 2] 3 = (1 . (2 . 3))`, `1` the atom `1`, `2`
  the comb `(2 . 3)`, `3` the atom `2`, `4` the atom `3`; no other handle is defined.
* `comb [1, 2] 3` is accepted by `combCheck` (`combCheck_accepts_123`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle

/-- The handle table of `comb [1, 2] 3`: `isAtom` answers `0` for the pairs `0`, `2` and `1`
otherwise; `left` maps `0 ↦ 1`, `2 ↦ 3`; `right` maps `0 ↦ 2`, `2 ↦ 4`; `word` maps `1 ↦ 1`,
`3 ↦ 2`, `4 ↦ 3`. -/
def combScript : Script := fun _ h args =>
  match Silmaril.Wasm.Game.HandleAccept.i32Arg args with
  | none => []
  | some x =>
    if h = combIx.isAtom then [Val.i32 (if x = 0 ∨ x = 2 then 0 else 1)]
    else if h = combIx.left then [Val.i32 (x + 1)]
    else if h = combIx.right then [Val.i32 (x + 2)]
    else if h = combIx.word then [Val.i64 (if x = 1 then 1 else if x = 3 then 2 else 3)]
    else []

/-- The environment of `combScript`: handle `0` denotes `comb [1, 2] 3`. -/
def combEnv : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64)) := fun h =>
  if h = 0 then some (comb [1, 2] 3) else if h = 1 then some (.atom 1)
  else if h = 2 then some (comb [2] 3) else if h = 3 then some (.atom 2)
  else if h = 4 then some (.atom 3) else none

open Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2 (mem_tree2Lang_of_replay)

theorem combCheck_accepts_123 {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c') :
    comb [1, 2] 3 ∈ moduleTree2Lang P combCheck combIx .trap .callTrap {combEnv} :=
  mem_tree2Lang_of_replay combCheck_instance hP combIx .trap .callTrap (Set.mem_singleton _)
    combScript refFuel 16 ⟨0, by decide +kernel⟩ 0 0 rfl (by decide +kernel) (by decide +kernel)

theorem combCheck_accepts_123_spec (nd : Bool) :
    comb [1, 2] 3 ∈
      moduleTree2Lang (Profile.spec nd {}) combCheck combIx .trap .callTrap {combEnv} :=
  combCheck_accepts_123 fun _ _ hs => Step.deterministic_refines_spec nd hs

end Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers
