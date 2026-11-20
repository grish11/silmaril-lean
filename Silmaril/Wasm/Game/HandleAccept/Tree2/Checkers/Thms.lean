module

public import Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers.Defs
public import Silmaril.Wasm.Game.HandleAccept.Tree2.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2.Comb

/-!
# Executable binary-tree reader checker: what is proved

* `combCheck` validates and instantiates (`combCheck_instance`, by kernel evaluation of
  `Silmaril.Wasm.Verify.instance?`).
* **Hoare-logic specification** (`combCheck_sat`): in every environment `ρ` and for every
  profile, the instance meets the binary-tree reader specification `tree2ISpec combIx ρ combL`
  (`Silmaril.Wasm.Logic.GameLink.GameSat`, partial correctness) with the store invariant
  `consInv` (proof in `Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2`).
* **Soundness** (`combCheck_sound`): its reader language under the trapping read policy, for
  every accept policy but `ub` (in particular the Wasm-facing call-local trap `callTrap`), in
  every set of environments, for every profile and every sequence of export calls, is included
  in the right combs of words `combL`, through `tree2Lang_sound_of_forall`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers

open Silmaril.Wasm Silmaril.Formats
open Silmaril.Wasm.Game.HandleAccept.Checkers (consInv)

theorem combCheck_instance : (Verify.instance? combCheck).isSome = true := by decide +kernel

/-- **`combCheck` meets the binary-tree reader specification of `combL`.** -/
theorem combCheck_sat : ∀ P ρ, Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf combCheck)
    (consInv combCheck) (tree2ISpec combIx ρ combL) (Silmaril.Wasm.Game.HandleAccept.topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2.combCheck_sat

/-- **`combCheck` accepts only right combs of words.** -/
theorem combCheck_sound (P : Profile) {oa : Silmaril.Accept.Handle.OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64)))) :
    moduleTree2Lang P combCheck combIx .trap oa Envs ⊆ combL :=
  tree2Lang_sound_of_forall (fun ρ _ => combCheck_sat P ρ) rfl hoa

end Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers
