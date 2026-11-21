module

public import Silmaril.Wasm.Game.HandleAccept.Nary.Checkers.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.Pair
import Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.Sorted

/-!
# Executable n-ary reader checkers: what is proved

* `wordsNCheck` and `sortedNCheck` validate and instantiate (`wordsNCheck_instance`,
  `sortedNCheck_instance`, by kernel evaluation of `Silmaril.Wasm.Verify.instance?`).
* The languages: `sortedNL ⊆ wordsNL` (`sortedNL_subset_wordsNL`); `wordsNL` is the lists
  `SExp.ofList (ws.map .atom)` (`mem_wordsNL`).
* **Hoare-logic specifications** (`pairCheck_sat`, `wordsNCheck_sat`, `sortedNCheck_sat`): in
  every environment `ρ` and for every profile, each module's instance meets the n-ary reader
  specification `sexpISpec pairIx ρ L` of its language (`Silmaril.Wasm.Logic.GameLink.GameSat`,
  partial correctness) with the store invariant `consInv` (proofs in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Nary`).
* **Soundness**: each module's reader language under the trapping read policy, for every accept
  policy but `ub` (in particular the Wasm-facing call-local trap `callTrap`, where a trapped
  export call is followed by further export calls), in every set of environments, for every
  profile and every sequence of export calls, is included in its
  language (`pairCheck_sound`: two-element lists `pairL`; `wordsNCheck_sound`: lists of words;
  `sortedNCheck_sound`: sorted lists of words), through `sexpLang_sound_of_forall`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Nary.Checkers

open Silmaril.Wasm Silmaril.Formats Silmaril.Wasm.Game.HandleAccept.Nary.Examples
open Silmaril.Wasm.Game.HandleAccept.Checkers (consInv)

theorem wordsNCheck_instance : (Verify.instance? wordsNCheck).isSome = true := by decide +kernel
theorem sortedNCheck_instance : (Verify.instance? sortedNCheck).isSome = true := by decide +kernel

/-! ## Languages -/

theorem mem_wordsNL {x : SExp (BitVec 64)} :
    x ∈ wordsNL ↔ ∃ ws : List (BitVec 64), x = SExp.ofList (ws.map .atom) :=
  Iff.rfl

theorem sortedNL_subset_wordsNL : sortedNL ⊆ wordsNL := fun _ ⟨ws, h, _⟩ => ⟨ws, h⟩

/-! ## Hoare-logic specifications -/

/-- **`pairCheck` meets the n-ary reader specification of `pairL`.** -/
theorem pairCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf pairCheck)
    (consInv pairCheck) (sexpISpec pairIx ρ pairL) (Silmaril.Wasm.Game.HandleAccept.topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.pairCheck_sat

/-- **`wordsNCheck` meets the n-ary reader specification of `wordsNL`.** -/
theorem wordsNCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P
    (Verify.instOf wordsNCheck) (consInv wordsNCheck) (sexpISpec pairIx ρ wordsNL)
    (Silmaril.Wasm.Game.HandleAccept.topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.wordsNCheck_sat

/-- **`sortedNCheck` meets the n-ary reader specification of `sortedNL`.** -/
theorem sortedNCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P
    (Verify.instOf sortedNCheck) (consInv sortedNCheck) (sexpISpec pairIx ρ sortedNL)
    (Silmaril.Wasm.Game.HandleAccept.topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.sortedNCheck_sat

/-! ## Soundness -/

/-- **`pairCheck` accepts only two-element lists.** -/
theorem pairCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))) :
    moduleSExpLang P pairCheck pairIx .trap oa Envs ⊆ pairL :=
  sexpLang_sound_of_forall (fun ρ _ => pairCheck_sat P ρ) rfl hoa

/-- **`wordsNCheck` accepts only lists of words.** -/
theorem wordsNCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))) :
    moduleSExpLang P wordsNCheck pairIx .trap oa Envs ⊆ wordsNL :=
  sexpLang_sound_of_forall (fun ρ _ => wordsNCheck_sat P ρ) rfl hoa

/-- **`sortedNCheck` accepts only sorted lists of words.** -/
theorem sortedNCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))) :
    moduleSExpLang P sortedNCheck pairIx .trap oa Envs ⊆ sortedNL :=
  sexpLang_sound_of_forall (fun ρ _ => sortedNCheck_sat P ρ) rfl hoa

end Silmaril.Wasm.Game.HandleAccept.Nary.Checkers
