module

public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecProper.Lang
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.RecProper.Sat

/-!
# The nested-list checker: what is proved

* `recProperCheck` validates and instantiates (`recProperCheck_instance`).
* **The language** `nestL` lies strictly between the proper lists of words and the recursively
  proper lists: `wordsL ⊂ nestL ⊂ recProperL` (`wordsL_subset_nestL`, `nestL_subset_recProperL`;
  strictness: `nested123 = ((1 2) 3)` is in `nestL` but not in `wordsL`, and `(((1)))` is
  recursively proper but not in `nestL`). `dottedElem = ((() . 1))`, a spine-proper list
  accepted by `properCheck`, is not in `nestL` (`dottedElem_not_mem_nestL`).
* **Hoare-logic specification** (`recProperCheck_sat`): in every environment `ρ` and every
  profile, the instance meets the cons reader specification `consISpec consIx ρ nestL` with the
  store invariant `consInv` (two nested loops; proof in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers`).
* **Soundness**: under the trapping read policy and every accept policy but `ub` (in particular
  the call-local trap `callTrap`), in every set of environments and every profile, the checker
  accepts only members of `nestL` (`recProperCheck_sound`), hence only recursively proper lists
  (`recProperCheck_sound_rec`); it accepts no run on `dottedElem`
  (`recProperCheck_rejects_dottedElem`), unlike `properCheck`
  (`Examples.properCheck_accepts_dottedElem`).

**Depth.** The bound is `nestL`, not `recProperL`: the check is depth-bounded (elements are atoms
or proper lists of atoms). The checker for the whole of `recProperL`, using Wasm recursion, is
`Silmaril.Wasm.Game.HandleAccept.Checkers.RecFull` (`recFullCheck_sound`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle

theorem recProperCheck_instance : (Verify.instance? recProperCheck).isSome = true := by
  decide +kernel

/-! ## The language -/

theorem wordsL_subset_nestL : wordsL ⊆ nestL := by
  rintro _ ⟨ws, rfl⟩
  exact Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.ofAtoms_nestList ws

theorem nestL_subset_recProperL : nestL ⊆ recProperL :=
  fun _ h => Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.nestList_properList h

theorem nestL_subset_properL : nestL ⊆ properL :=
  fun _ h => recProperL_subset_properL (nestL_subset_recProperL h)

theorem ofAtoms_mem_nestL (ws : List (BitVec 64)) : SExp2.ofAtoms ws ∈ nestL :=
  wordsL_subset_nestL ⟨ws, rfl⟩

theorem nested123_mem_nestL : nested123 ∈ nestL :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.nested123_nestList

theorem nested123_not_mem_wordsL : nested123 ∉ wordsL :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.nested123_not_mem_wordsL

theorem wordsL_ssubset_nestL : wordsL ⊂ nestL :=
  ⟨wordsL_subset_nestL, fun h => nested123_not_mem_wordsL (h nested123_mem_nestL)⟩

/-- `(((1)))` is recursively proper but nested three deep. -/
theorem deep1_not_mem_nestL :
    SExp2.ofList [SExp2.ofList [SExp2.ofAtoms [(1 : BitVec 64)]]] ∉ nestL :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.deep1_not_nestList

theorem deep1_mem_recProperL :
    SExp2.ofList [SExp2.ofList [SExp2.ofAtoms [(1 : BitVec 64)]]] ∈ recProperL := by
  show SExp2.ProperList _
  decide

theorem nestL_ssubset_recProperL : nestL ⊂ recProperL :=
  ⟨nestL_subset_recProperL, fun h => deep1_not_mem_nestL (h deep1_mem_recProperL) |>.elim⟩

theorem dottedElem_not_mem_nestL : dottedElem ∉ nestL :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.dottedElem_not_nestList

/-! ## Specification and soundness -/

/-- **`recProperCheck` meets the cons reader specification of `nestL`.** -/
theorem recProperCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P
    (Verify.instOf recProperCheck) (consInv recProperCheck) (consISpec consIx ρ nestL)
    (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.recProperCheck_sat

/-- **`recProperCheck` accepts only members of `nestL`.** -/
theorem recProperCheck_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P recProperCheck consIx .trap oa Envs ⊆ nestL :=
  consLang_sound_of_forall (fun ρ _ => recProperCheck_sat P ρ) rfl hoa

/-- **`recProperCheck` accepts only recursively proper lists.** -/
theorem recProperCheck_sound_rec (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsLang P recProperCheck consIx .trap oa Envs ⊆ recProperL :=
  fun _ h => nestL_subset_recProperL (recProperCheck_sound P hoa Envs h)

/-- **`recProperCheck` rejects `dottedElem`** in every environment and profile. -/
theorem recProperCheck_rejects_dottedElem (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    dottedElem ∉ moduleConsLang P recProperCheck consIx .trap oa Envs :=
  fun h => dottedElem_not_mem_nestL (recProperCheck_sound P hoa Envs h)

end Silmaril.Wasm.Game.HandleAccept.Checkers
