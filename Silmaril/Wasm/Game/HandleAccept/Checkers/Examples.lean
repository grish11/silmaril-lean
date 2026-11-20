module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Replay

/-!
# Executable reader checkers: examples (non-vacuity)

The soundness theorems of `Silmaril.Wasm.Game.HandleAccept.Checkers.Thms` bound each checker's
reader language from above. Here the languages are shown non-empty, and the checkers different,
by running them: each positive example replays the call `check(0)` (the replay refuter's
candidate argument `0`, `Silmaril.Wasm.Resource.replayExport`) on the verified interpreter, with
the import answers of a concrete handle table (`cellScript`), by kernel evaluation, and checks
that every decoded read is correct in a concrete environment and that handle `0` is accepted
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.mem_consLang_of_replay`).

**Profiles.** The replay is a play of the instance's strategy for every profile `P` admitting
the deterministic steps of the interpreter (`profile refOracle`: deterministic numerics, failing
`memory.grow`), hypothesis `hP`; this holds for every specification profile `Profile.spec nd {}`
(`Step.deterministic_refines_spec`), stated as the `_spec` corollaries.

* `listEnv w₁ w₂`: handle `0` denotes the list of words `(w₁ w₂)`, `1` the atom `w₁`, `2` the
  tail `(w₂)`, `3` the atom `w₂`, `4` nil; no other handle is defined.
* `(1 2)` is accepted by all three checkers (`properCheck_accepts_12`, `wordsCheck_accepts_12`,
  `sortedCheck_accepts_12`).
* `(2 1)` is accepted by `wordsCheck` (`wordsCheck_accepts_21`) but by no run of `sortedCheck`
  in any environment (`sortedCheck_rejects_21`, by soundness).
* `dottedElem = ((() . 1))` is accepted by `properCheck` (`properCheck_accepts_dottedElem`) but by
  no run of `wordsCheck` (`wordsCheck_rejects_dottedElem`).
* An atom is accepted by no run of `properCheck` (`properCheck_rejects_atom`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle

/-! ## Scripted environments -/

/-- Handle environments of words. -/
abbrev HEnv := Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))

/-- What the environment answers about a handle: its kind code (`0` nil, `1` atom, `2` cons),
the handles of its `car` and `cdr`, and its word. -/
structure Cell where
  kind : BitVec 32
  car : BitVec 32 := 0
  cdr : BitVec 32 := 0
  word : BitVec 64 := 0

/-- The import answers of a handle table: `kind`, `car`, `cdr` and `word` of the argument handle
as in the table, nothing for `accept`. -/
def cellScript (ix : ConsImports) (tab : BitVec 32 → Cell) : Script := fun _ h args =>
  match i32Arg args with
  | none => []
  | some x =>
    if h = ix.kind then [Val.i32 (tab x).kind] else if h = ix.car then [Val.i32 (tab x).car]
    else if h = ix.cdr then [Val.i32 (tab x).cdr] else if h = ix.word then [Val.i64 (tab x).word]
    else []

/-- The handles of the list `(w₁ w₂)`. -/
def listTab (w₁ w₂ : BitVec 64) (h : BitVec 32) : Cell :=
  if h = 0 then ⟨2, 1, 2, 0⟩ else if h = 1 then ⟨1, 0, 0, w₁⟩
  else if h = 2 then ⟨2, 3, 4, 0⟩ else if h = 3 then ⟨1, 0, 0, w₂⟩ else ⟨0, 0, 0, 0⟩

/-- The environment of `listTab`: handle `0` denotes `(w₁ w₂)`. -/
def listEnv (w₁ w₂ : BitVec 64) : HEnv := fun h =>
  if h = 0 then some (SExp2.ofAtoms [w₁, w₂]) else if h = 1 then some (.atom w₁)
  else if h = 2 then some (SExp2.ofAtoms [w₂]) else if h = 3 then some (.atom w₂)
  else if h = 4 then some .nil else none

/-- The handles of `dottedElem = ((() . 1))`. -/
def dotTab (h : BitVec 32) : Cell :=
  if h = 0 then ⟨2, 2, 1, 0⟩ else if h = 2 then ⟨2, 1, 3, 0⟩ else if h = 3 then ⟨1, 0, 0, 1⟩
  else ⟨0, 0, 0, 0⟩

/-- The environment of `dotTab`: handle `0` denotes `dottedElem`. -/
def dotEnv : HEnv := fun h =>
  if h = 0 then some dottedElem else if h = 1 then some .nil
  else if h = 2 then some (.cons .nil (.atom 1)) else if h = 3 then some (.atom 1) else none

/-! ## Positive examples -/

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
include hP

open Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers (mem_consLang_of_replay)

theorem properCheck_accepts_12 :
    SExp2.ofAtoms [1, 2] ∈ moduleConsLang P properCheck consIx .trap .callTrap {listEnv 1 2} :=
  mem_consLang_of_replay properCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx (listTab 1 2)) refFuel 16 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wordsCheck_accepts_12 :
    SExp2.ofAtoms [1, 2] ∈ moduleConsLang P wordsCheck consIx .trap .callTrap {listEnv 1 2} :=
  mem_consLang_of_replay wordsCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx (listTab 1 2)) refFuel 16 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sortedCheck_accepts_12 :
    SExp2.ofAtoms [1, 2] ∈ moduleConsLang P sortedCheck consIx .trap .callTrap {listEnv 1 2} :=
  mem_consLang_of_replay sortedCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx (listTab 1 2)) refFuel 16 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem wordsCheck_accepts_21 :
    SExp2.ofAtoms [2, 1] ∈ moduleConsLang P wordsCheck consIx .trap .callTrap {listEnv 2 1} :=
  mem_consLang_of_replay wordsCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx (listTab 2 1)) refFuel 16 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem properCheck_accepts_dottedElem :
    dottedElem ∈ moduleConsLang P properCheck consIx .trap .callTrap {dotEnv} :=
  mem_consLang_of_replay properCheck_instance hP consIx .trap .callTrap (Set.mem_singleton _)
    (cellScript consIx dotTab) refFuel 16 ⟨0, by decide +kernel⟩ 0 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Positive

/-! ### At the specification profiles -/

theorem properCheck_accepts_12_spec (nd : Bool) : SExp2.ofAtoms [1, 2] ∈
    moduleConsLang (Profile.spec nd {}) properCheck consIx .trap .callTrap {listEnv 1 2} :=
  properCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem wordsCheck_accepts_12_spec (nd : Bool) : SExp2.ofAtoms [1, 2] ∈
    moduleConsLang (Profile.spec nd {}) wordsCheck consIx .trap .callTrap {listEnv 1 2} :=
  wordsCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem sortedCheck_accepts_12_spec (nd : Bool) : SExp2.ofAtoms [1, 2] ∈
    moduleConsLang (Profile.spec nd {}) sortedCheck consIx .trap .callTrap {listEnv 1 2} :=
  sortedCheck_accepts_12 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem wordsCheck_accepts_21_spec (nd : Bool) : SExp2.ofAtoms [2, 1] ∈
    moduleConsLang (Profile.spec nd {}) wordsCheck consIx .trap .callTrap {listEnv 2 1} :=
  wordsCheck_accepts_21 fun _ _ hs => Step.deterministic_refines_spec nd hs

theorem properCheck_accepts_dottedElem_spec (nd : Bool) :
    dottedElem ∈ moduleConsLang (Profile.spec nd {}) properCheck consIx .trap .callTrap {dotEnv} :=
  properCheck_accepts_dottedElem fun _ _ hs => Step.deterministic_refines_spec nd hs

/-! ## Negative examples (from soundness: every profile, every set of environments) -/

theorem not_sorted_21 : SExp2.ofAtoms [(2 : BitVec 64), 1] ∉ sortedL := by
  rintro ⟨ws, hws, hp⟩
  cases SExp2.ofAtoms_injective hws
  exact absurd hp (by decide)

theorem not_words_dottedElem : dottedElem ∉ wordsL := by
  rintro ⟨_ | ⟨w, ws⟩, hws⟩
  · cases hws
  · cases SExp2.cons.inj hws |>.1

theorem sortedCheck_rejects_21 (P : Profile) (Envs : Set (HEnv)) :
    SExp2.ofAtoms [2, 1] ∉ moduleConsLang P sortedCheck consIx .trap .callTrap Envs :=
  fun h => not_sorted_21 (sortedCheck_sound P (by decide) Envs h)

theorem wordsCheck_rejects_dottedElem (P : Profile)
    (Envs : Set (HEnv)) :
    dottedElem ∉ moduleConsLang P wordsCheck consIx .trap .callTrap Envs :=
  fun h => not_words_dottedElem (wordsCheck_sound P (by decide) Envs h)

theorem properCheck_rejects_atom (P : Profile) (Envs : Set (HEnv))
    (w : BitVec 64) : SExp2.atom w ∉ moduleConsLang P properCheck consIx .trap .callTrap Envs :=
  fun h => nomatch (properCheck_sound P (by decide) Envs h : SpineProperList (SExp2.atom w))

end Silmaril.Wasm.Game.HandleAccept.Checkers
