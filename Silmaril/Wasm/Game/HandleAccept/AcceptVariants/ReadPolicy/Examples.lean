module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Thms
public import Silmaril.Wasm.Resource.Replay.Defs
import Silmaril.Wasm.Execution.Core.SpecProfile
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Replay

/-!
# Non-trapping read policies at Wasm: runs and counterexamples

Each statement replays `check(5)` on the verified interpreter with a scripted host, in a fixed
environment, and checks every decoded read against the answers the read policy allows there
(`Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy.mem_errLang_of_replay`), for every profile
admitting the interpreter's deterministic steps.

* `carCheck_accepts`: in `ρok` (`5 ↦ (0)`, `6 ↦ 0`), `car(5) = 6`, `kind(6) = 1`: `carCheck`
  accepts `(0)` under `dflt errD`: the soundness bound `carCheck_sound` is not vacuous.
* **`carNoCheck_unsound_dflt`**: in `ρerr` (`5 ↦ 0`, `-1 ↦ 0`), `car(5)` is invalid and gets
  the error code `-1` (the only answer `dflt errD` allows); `carNoCheck` does not check it and
  asks `kind(-1)`, which is a valid query answered `1` (atom); it accepts the atom `0`, which is
  not a cons cell. The typed-error policy makes a module that ignores error codes unsound.
* **`carCheck_unsound_arbitrary`**: in `ρarb` (`5 ↦ 0`, `7 ↦ 0`), `car(5)` is invalid and,
  under `arbitrary`, may be answered `7`, which is not the error code; `kind(7) = 1`; `carCheck`
  accepts the atom `0`. Checking error codes is sound for typed errors only; under arbitrary
  answers no check of the answer can tell an invalid query apart (the Wasm counterpart of
  `Silmaril.Accept.Handle.Examples.arbitrary_uncertified`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.ReadPolicy

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle

/-- A script answering the callouts in order. -/
def seqScript (answers : List (List Val)) : Script := fun k _ _ => answers.getD k []

/-- `5 ↦ (0)`, `6 ↦ 0`. -/
def ρok : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)) := fun h =>
  if h = 5 then some (.cons (.atom 0) .nil) else if h = 6 then some (.atom 0) else none

/-- `5 ↦ 0`, `-1 ↦ 0`. -/
def ρerr : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)) := fun h =>
  if h = 5 ∨ h = -1 then some (.atom 0) else none

/-- `5 ↦ 0`, `7 ↦ 0`. -/
def ρarb : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)) := fun h =>
  if h = 5 ∨ h = 7 then some (.atom 0) else none

/-- The reads of the three runs: `car(5) = c`, `kind(c) = atom`. -/
def readsOk (c : BitVec 32) (ca : ConsA (BitVec 64) (BitVec 32)) :
    ConsQ (BitVec 32) → ConsA (BitVec 64) (BitVec 32) → Bool
  | .car h, .handle h' => decide (h = 5) && match ca with
    | .handle c' => decide (h' = c')
    | _ => false
  | .car h, .kind .nil => decide (h = 5) && match ca with
    | .kind .nil => true
    | _ => false
  | .kind h, .kind .atom => decide (h = c)
  | _, _ => false

section Positive

variable {P : Profile}
  (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
include hP

open Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy (mem_errLang_of_replay allowed_of_ok
  allowed_of_bad)

theorem carCheck_accepts :
    SExp2.cons (.atom 0) .nil ∈
      moduleErrLang P carCheck Checkers.consIx (.dflt errD) .callTrap Set.univ :=
  mem_errLang_of_replay carCheck_instance hP _ _ _ (Set.mem_univ ρok)
    (okR := readsOk 6 (.handle 6)) (okA := fun h => decide (h = 5))
    (fun q a h => by
      rcases q with q | q | q | q <;> rcases a with (_ | _ | _) | w | h' <;>
        simp [readsOk] at h
      · subst h; exact allowed_of_ok (by simp [consR, ρok]) ⟨.atom 0, by simp [ρok], rfl⟩
      · obtain ⟨rfl, rfl⟩ := h
        exact allowed_of_ok (by simp [consR, ρok]) ⟨.atom 0, .nil, by simp [ρok], by simp [ρok]⟩)
    (fun h hh => by simp at hh; subst hh; simp [ρok])
    (seqScript [[Val.i32 6], [Val.i32 1], []]) refFuel 4 ⟨0, by decide +kernel⟩ 5 5
    (by simp [ρok]) (by decide +kernel) (by decide +kernel)

/-- **Ignoring the error code is unsound under typed errors.** -/
theorem carNoCheck_unsound_dflt :
    SExp2.atom 0 ∈ moduleErrLang P carNoCheck Checkers.consIx (.dflt errD) .callTrap Set.univ ∧
      SExp2.atom 0 ∉ carAtomL :=
  ⟨mem_errLang_of_replay carNoCheck_instance hP _ _ _ (Set.mem_univ ρerr)
    (okR := readsOk (-1) (.kind .nil)) (okA := fun h => decide (h = 5))
    (fun q a h => by
      rcases q with q | q | q | q <;> rcases a with (_ | _ | _) | w | h' <;>
        simp [readsOk] at h
      · subst h; exact allowed_of_ok (by simp [consR, ρerr]) ⟨.atom 0, by simp [ρerr], rfl⟩
      · subst h; exact allowed_of_bad (by simp [consR, ρerr]) rfl (by simp [errD]))
    (fun h hh => by simp at hh; subst hh; simp [ρerr])
    (seqScript [[Val.i32 (-1)], [Val.i32 1], []]) refFuel 4 ⟨0, by decide +kernel⟩ 5 5
    (by simp [ρerr]) (by decide +kernel) (by decide +kernel),
   by rintro ⟨_, _, h⟩; cases h⟩

/-- **Checking the error code is not enough under arbitrary answers.** -/
theorem carCheck_unsound_arbitrary :
    SExp2.atom 0 ∈ moduleErrLang P carCheck Checkers.consIx .arbitrary .callTrap Set.univ ∧
      SExp2.atom 0 ∉ carAtomL :=
  ⟨mem_errLang_of_replay carCheck_instance hP _ _ _ (Set.mem_univ ρarb)
    (okR := readsOk 7 (.handle 7)) (okA := fun h => decide (h = 5))
    (fun q a h => by
      rcases q with q | q | q | q <;> rcases a with (_ | _ | _) | w | h' <;>
        simp [readsOk] at h
      · subst h; exact allowed_of_ok (by simp [consR, ρarb]) ⟨.atom 0, by simp [ρarb], rfl⟩
      · obtain ⟨rfl, rfl⟩ := h
        exact allowed_of_bad (by simp [consR, ρarb]) rfl (Set.mem_univ _))
    (fun h hh => by simp at hh; subst hh; simp [ρarb])
    (seqScript [[Val.i32 7], [Val.i32 1], []]) refFuel 4 ⟨0, by decide +kernel⟩ 5 5
    (by simp [ρarb]) (by decide +kernel) (by decide +kernel),
   by rintro ⟨_, _, h⟩; cases h⟩

end Positive

end Silmaril.Wasm.Game.HandleAccept.ReadPolicy
