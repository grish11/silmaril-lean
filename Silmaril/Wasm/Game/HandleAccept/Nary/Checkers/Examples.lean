module

public import Silmaril.Wasm.Game.HandleAccept.Nary.Checkers.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.Replay

/-!
# Executable n-ary reader checkers: examples (non-vacuity)

The soundness theorems of `Silmaril.Wasm.Game.HandleAccept.Nary.Checkers.Thms` bound each
checker's reader language from above. Here the languages are shown non-empty by running the
checkers: each positive example replays the call `check(0)` (candidate argument `0`,
`Silmaril.Wasm.Resource.replayExport`) on the verified interpreter, with the import answers of a
concrete handle table (`sxScript`), by kernel evaluation, and checks that every decoded read is
correct in a concrete environment and that handle `0` is accepted
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.mem_sexpLang_of_replay`).

**Profiles.** As in `Silmaril.Wasm.Game.HandleAccept.Checkers.Examples`: every profile `P`
admitting the deterministic steps of the interpreter (hypothesis `hP`), in particular every
specification profile `Profile.spec nd {}` (the `_spec` corollaries).

* `nListEnv w₁ w₂`: handle `0` denotes the list `(w₁ w₂)`, `1` the atom `w₁`, `2` the atom `w₂`;
  no other handle is defined.
* `(1 2)` is accepted by `pairCheck`, `wordsNCheck` and `sortedNCheck` (`pairCheck_accepts_12`,
  `wordsNCheck_accepts_12`, `sortedNCheck_accepts_12`); `(2 1)` by `wordsNCheck`
  (`wordsNCheck_accepts_21`) but by no run of `sortedNCheck` (`sortedNCheck_rejects_21`, by
  soundness).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Nary.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept.Nary.Examples

/-! ## Scripted environments -/

/-- The import answers of a handle table: `kind`, `count`, `child` and `word` of the argument
handles as given, nothing for `accept`. -/
def sxScript (ix : SxRImports) (kind count : BitVec 32 → BitVec 32)
    (child : BitVec 32 → BitVec 32 → BitVec 32) (word : BitVec 32 → BitVec 64) : Script :=
  fun _ h args =>
    if h = ix.child then
      match i32Two args with
      | some (a, i) => [Val.i32 (child a i)]
      | none => []
    else
      match Silmaril.Wasm.Game.HandleAccept.i32Arg args with
      | none => []
      | some x =>
        if h = ix.kind then [Val.i32 (kind x)] else if h = ix.count then [Val.i32 (count x)]
        else if h = ix.word then [Val.i64 (word x)] else []

/-- The handle table of the list `(w₁ w₂)`: `0` the list, `1` and `2` its atoms. -/
def nListScript (w₁ w₂ : BitVec 64) : Script :=
  sxScript pairIx (fun h => if h = 0 then 1 else 0) (fun h => if h = 0 then 2 else 0)
    (fun _ i => i + 1) (fun h => if h = 1 then w₁ else w₂)

/-- The environment of `nListScript`: handle `0` denotes `(w₁ w₂)`. -/
def nListEnv (w₁ w₂ : BitVec 64) : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)) :=
  fun h =>
    if h = 0 then some (SExp.ofAtoms [w₁, w₂]) else if h = 1 then some (.atom w₁)
    else if h = 2 then some (.atom w₂) else none

/-! ## Positive examples -/

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
include hP

open Silmaril.Proofs.Wasm.Game.HandleAccept.Nary (mem_sexpLang_of_replay)

theorem pairCheck_accepts_12 :
    SExp.ofAtoms [1, 2] ∈ moduleSExpLang P pairCheck pairIx .trap .callTrap {nListEnv 1 2} :=
  mem_sexpLang_of_replay pairCheck_instance hP pairIx .trap .callTrap (Set.mem_singleton _)
    (nListScript 1 2) refFuel 16 ⟨0, by decide +kernel⟩ 0 0 rfl
    (by decide +kernel) (by decide +kernel)

theorem wordsNCheck_accepts_12 :
    SExp.ofAtoms [1, 2] ∈ moduleSExpLang P wordsNCheck pairIx .trap .callTrap {nListEnv 1 2} :=
  mem_sexpLang_of_replay wordsNCheck_instance hP pairIx .trap .callTrap (Set.mem_singleton _)
    (nListScript 1 2) refFuel 16 ⟨0, by decide +kernel⟩ 0 0 rfl
    (by decide +kernel) (by decide +kernel)

theorem sortedNCheck_accepts_12 :
    SExp.ofAtoms [1, 2] ∈ moduleSExpLang P sortedNCheck pairIx .trap .callTrap {nListEnv 1 2} :=
  mem_sexpLang_of_replay sortedNCheck_instance hP pairIx .trap .callTrap (Set.mem_singleton _)
    (nListScript 1 2) refFuel 16 ⟨0, by decide +kernel⟩ 0 0 rfl
    (by decide +kernel) (by decide +kernel)

theorem wordsNCheck_accepts_21 :
    SExp.ofAtoms [2, 1] ∈ moduleSExpLang P wordsNCheck pairIx .trap .callTrap {nListEnv 2 1} :=
  mem_sexpLang_of_replay wordsNCheck_instance hP pairIx .trap .callTrap (Set.mem_singleton _)
    (nListScript 2 1) refFuel 16 ⟨0, by decide +kernel⟩ 0 0 rfl
    (by decide +kernel) (by decide +kernel)

end Positive

/-! ### At the specification profiles -/

theorem pairCheck_accepts_12_spec (nd : Bool) : SExp.ofAtoms [1, 2] ∈
    moduleSExpLang (Profile.spec nd {}) pairCheck pairIx .trap .callTrap {nListEnv 1 2} :=
  pairCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem wordsNCheck_accepts_12_spec (nd : Bool) : SExp.ofAtoms [1, 2] ∈
    moduleSExpLang (Profile.spec nd {}) wordsNCheck pairIx .trap .callTrap {nListEnv 1 2} :=
  wordsNCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem sortedNCheck_accepts_12_spec (nd : Bool) : SExp.ofAtoms [1, 2] ∈
    moduleSExpLang (Profile.spec nd {}) sortedNCheck pairIx .trap .callTrap {nListEnv 1 2} :=
  sortedNCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem wordsNCheck_accepts_21_spec (nd : Bool) : SExp.ofAtoms [2, 1] ∈
    moduleSExpLang (Profile.spec nd {}) wordsNCheck pairIx .trap .callTrap {nListEnv 2 1} :=
  wordsNCheck_accepts_21 fun _ _ hs => Step.deterministic_refines_spec nd hs

/-! ## Negative example (from soundness: every profile, every set of environments) -/

theorem not_sortedN_21 : SExp.ofAtoms [(2 : BitVec 64), 1] ∉ sortedNL := by
  rintro ⟨ws, hws, hp⟩
  cases SExp.ofAtoms_injective hws
  exact absurd hp (by decide)

theorem sortedNCheck_rejects_21 (P : Profile)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))) :
    SExp.ofAtoms [2, 1] ∉ moduleSExpLang P sortedNCheck pairIx .trap .callTrap Envs :=
  fun h => not_sortedN_21 (sortedNCheck_sound P (by decide) Envs h)

end Silmaril.Wasm.Game.HandleAccept.Nary.Checkers
