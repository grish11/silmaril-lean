module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Checkers.Defs
public import Silmaril.Wasm.Game.HandleAccept.Parse.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Parse.OneShot

/-!
# A one-shot parser with a proved relation: what is proved

* `nzParse` validates and instantiates (`nzParse_instance`).
* **Hoare-logic specification** (`nzParse_sat`): in every environment `ρ` and every profile, the
  instance meets the parse specification `parseESpec nzIx 0 ρ (nzR T)` with the store invariant
  `nzInv` (proof in `Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers`): `parse(x)`
  answers the sentinel `0` unless `x ≠ 0`.
* **Soundness** (`nzParse_sound`): for every profile, every set of environments and every parse
  policy with sentinel `0` and no UB on unresolved handles, every input/tree pair of
  `nzParse` is a single nonzero word (with any tree), through `moduleParseRel_sound_of_forall`.
  `nzParse_input` restates it on inputs.

The tree is unconstrained: parse specifications do not constrain the writer import `word`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers

open Silmaril.Wasm Silmaril.Accept.Parse Silmaril.Wasm.Game.HandleAccept

theorem nzParse_instance : (Verify.instance? nzParse).isSome = true := by decide +kernel

/-- **`nzParse` meets the parse specification of `nzR`** (sentinel `0`). -/
theorem nzParse_sat (P : Profile) {T : Type} (ρ : Silmaril.Accept.Handle.Env (BitVec 32) T) :
    Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf nzParse)
      nzInv (topISpec _) (parseESpec nzIx 0 ρ (nzR T)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.Checkers.nzParse_sat P ρ

/-- **`nzParse` relates only single nonzero words.** -/
theorem nzParse_sound {T : Type} (P : Profile) {pol : PPolicy (BitVec 32)} (h0 : pol.sentinel = 0)
    (hb : pol.onBadHandle ≠ .ub) (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) T)) :
    moduleParseRel P nzParse nzIx pol Envs ⊆ nzR T :=
  moduleParseRel_sound_of_forall (Inv := nzInv) (fun ρ _ => h0 ▸ nzParse_sat P ρ) rfl
    ⟨rfl, rfl, rfl, rfl⟩ hb

/-- The inputs of `nzParse`: single nonzero words. -/
theorem nzParse_input {T : Type} (P : Profile) {pol : PPolicy (BitVec 32)} (h0 : pol.sentinel = 0)
    (hb : pol.onBadHandle ≠ .ub) (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) T)) :
    inputLang (moduleParseRel P nzParse nzIx pol Envs) ⊆ {w | ∃ v, w = [v] ∧ v ≠ 0} := by
  rintro _ ⟨q, hq, rfl⟩
  exact nzParse_sound P h0 hb Envs hq

end Silmaril.Wasm.Game.HandleAccept.Parsing.Checkers
