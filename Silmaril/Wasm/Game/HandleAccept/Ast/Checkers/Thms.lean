module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Checkers.Defs
public import Silmaril.Wasm.Logic.GameLink.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.Checker

/-!
# An executable AST reader checker: what is proved

* `addCheck` validates and instantiates (`addCheck_instance`, by kernel evaluation of
  `Silmaril.Wasm.Verify.instance?`).
* **Hoare-logic specification** (`addCheck_sat`): in every environment `ρ` and for every
  profile, the instance meets the AST reader specification `astISpec arithRIx ρ addL`
  (`Silmaril.Wasm.Logic.GameLink.GameSat`, partial correctness) with the store invariant
  `consInv addCheck` (the store's functions are those of the instance; proof in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.Checker`).
* **Soundness** (`addCheck_sound`): its reader language under the trapping read policy, for
  every accept policy but `ub` (in particular the Wasm-facing call-local trap `callTrap`), in
  every set of environments, for every profile and every sequence of export calls, is included
  in `addL`, the trees `add(num a, num b)`, through `astLang_sound_of_forall`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Ast.Checkers

open Silmaril.Wasm Silmaril.Formats Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Ast.Examples

theorem addCheck_instance : (Verify.instance? addCheck).isSome = true := by decide +kernel

/-- **`addCheck` meets the AST reader specification of `addL`.** -/
theorem addCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf addCheck)
    (Silmaril.Wasm.Game.HandleAccept.Checkers.consInv addCheck) (astISpec arithRIx ρ addL)
    (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.Checker.addCheck_sat

/-- **`addCheck` accepts only the trees `add(num a, num b)`.** -/
theorem addCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (AST arithSig.toAstSig))) :
    moduleAstLang P addCheck arithRIx .trap oa Envs ⊆ addL :=
  astLang_sound_of_forall (fun ρ _ => addCheck_sat P ρ) rfl hoa

end Silmaril.Wasm.Game.HandleAccept.Ast.Checkers
