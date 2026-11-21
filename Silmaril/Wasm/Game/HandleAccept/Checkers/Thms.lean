module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs
public import Silmaril.Wasm.Game.HandleAccept.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Lang
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Words
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Sorted

/-!
# Executable reader checkers: what is proved

* The three modules validate and instantiate (`properCheck_instance`, …, by kernel evaluation of
  `Silmaril.Wasm.Verify.instance?`), with the five cons imports in order.
* The languages: `sortedL ⊆ wordsL ⊆ properL`; `properL` is the spine-proper lists
  (`spineProperList_iff`: exactly the `SExp2.ofList xs`), and strictly contains the recursively
  proper lists `recProperL` (`recProperL_ssubset_properL`): a list may have a dotted pair as an
  element (`dottedElem_mem_properL`, `dottedElem_not_mem_recProperL`), but not a dotted outer
  `cdr` (`dottedTail_not_mem_properL`).
* **Hoare-logic specifications** (`properCheck_sat`, `wordsCheck_sat`, `sortedCheck_sat`): in
  every environment `ρ` and for every profile, each checker's instance meets the cons reader
  specification `consISpec consIx ρ L` of its language (`Silmaril.Wasm.Logic.GameLink.GameSat`,
  partial correctness) with the store invariant `consInv` (proofs in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers`).
* **Soundness**: each checker's reader language under the trapping read policy, for every accept
  policy but `ub` (in particular the Wasm-facing call-local trap `callTrap`, where a trapped
  export call is followed by further export calls), in every set of environments, for every
  profile and every sequence of export calls, is included in its
  language (`properCheck_sound`, `wordsCheck_sound`, `sortedCheck_sound`), through
  `consLang_sound_of_forall` and `Silmaril.Wasm.Logic.GameLink.strategy_sound`.

`properCheck` walks the `cdr` spine only: it checks spine-properness, not recursive
properness.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle

theorem properCheck_instance : (Verify.instance? properCheck).isSome = true := by decide +kernel
theorem wordsCheck_instance : (Verify.instance? wordsCheck).isSome = true := by decide +kernel
theorem sortedCheck_instance : (Verify.instance? sortedCheck).isSome = true := by decide +kernel

theorem properCheck_imports :
    (Verify.instOf properCheck).imports.length = 5 := by decide +kernel

/-! ## Languages -/

theorem ofAtoms_properList (ws : List (BitVec 64)) : SExp2.ProperList (SExp2.ofAtoms ws) :=
  SExp2.properList_ofList fun _ hx => by
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact .inl (.atom w)

/-- Spine-proper lists are the lists `SExp2.ofList xs` of arbitrary elements. -/
theorem spineProperList_iff {α : Type} {x : SExp2 α} :
    SpineProperList x ↔ ∃ xs, x = SExp2.ofList xs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.spineProperList_iff

/-- Recursively proper lists are spine-proper. -/
theorem spineProperList_of_properList {α : Type} {x : SExp2 α} (h : SExp2.ProperList x) :
    SpineProperList x :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.spineProperList_of_properList h

theorem recProperL_subset_properL : recProperL ⊆ properL :=
  fun _ h => spineProperList_of_properList h

/-- A list whose only element is the dotted pair `(() . 1)`. -/
def dottedElem : SExp2 (BitVec 64) := .cons (.cons .nil (.atom 1)) .nil

/-- The dotted pair `(() . 1)`: its outer `cdr` is an atom. -/
def dottedTail : SExp2 (BitVec 64) := .cons .nil (.atom 1)

theorem dottedElem_mem_properL : dottedElem ∈ properL := .cons _ .nil

theorem dottedElem_not_mem_recProperL : dottedElem ∉ recProperL := by
  show ¬ SExp2.ProperList dottedElem
  decide

theorem dottedTail_not_mem_properL : dottedTail ∉ properL := fun h => by
  cases h with
  | cons _ h => cases h

theorem recProperL_ssubset_properL : recProperL ⊂ properL :=
  ⟨recProperL_subset_properL, fun h => dottedElem_not_mem_recProperL (h dottedElem_mem_properL)⟩

theorem sortedL_subset_wordsL : sortedL ⊆ wordsL := fun _ ⟨ws, h, _⟩ => ⟨ws, h⟩

theorem wordsL_subset_properL : wordsL ⊆ properL := by
  rintro _ ⟨ws, rfl⟩
  exact spineProperList_iff.2 ⟨_, rfl⟩

/-! ## Hoare-logic specifications -/

/-- **`properCheck` meets the cons reader specification of `properL`.** -/
theorem properCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf properCheck)
    (consInv properCheck) (consISpec consIx ρ properL) (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.properCheck_sat

/-- **`wordsCheck` meets the cons reader specification of `wordsL`.** -/
theorem wordsCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf wordsCheck)
    (consInv wordsCheck) (consISpec consIx ρ wordsL) (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.wordsCheck_sat

/-- **`sortedCheck` meets the cons reader specification of `sortedL`.** -/
theorem sortedCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf sortedCheck)
    (consInv sortedCheck) (consISpec consIx ρ sortedL) (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.sortedCheck_sat

/-! ## Soundness -/

/-- **`properCheck` accepts only spine-proper lists.** -/
theorem properCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P properCheck consIx .trap oa Envs ⊆ properL :=
  consLang_sound_of_forall (fun ρ _ => properCheck_sat P ρ) rfl hoa

/-- **`wordsCheck` accepts only lists of words.** -/
theorem wordsCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P wordsCheck consIx .trap oa Envs ⊆ wordsL :=
  consLang_sound_of_forall (fun ρ _ => wordsCheck_sat P ρ) rfl hoa

/-- **`sortedCheck` accepts only sorted lists of words.** -/
theorem sortedCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P sortedCheck consIx .trap oa Envs ⊆ sortedL :=
  consLang_sound_of_forall (fun ρ _ => sortedCheck_sat P ρ) rfl hoa

end Silmaril.Wasm.Game.HandleAccept.Checkers
