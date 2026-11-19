module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Defs
public import Silmaril.Wasm.Game.HandleAccept.Checkers.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.TwoWords

/-!
# A writer module with a proved language: what is proved

* `twoWords` validates and instantiates (`twoWords_instance`).
* **Hoare-logic specification** (`twoWords_sat`): in every fixed environment `ρ` and every
  profile, the instance of `twoWords` meets the cons writer specification
  `writerISpec consW none … ρ twoWordsL` (no sentinel: every answered write returns a handle
  denoting the built tree) with the store invariant `consInv` (proof in
  `Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords`).
* **Soundness**: for every profile and every policy **without a failure sentinel**
  (`pol.sentinel = none`), the trees `twoWords` accepts are the lists `(x x+1)`: in the store
  semantics without UB (`twoWords_sound`) and over any set of fixed environments
  (`twoWords_fixed_sound`). With a sentinel, a failed write could reach `cons` or `accept`;
  `twoWords` does not test for one.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Writers.Builders

open Silmaril.Wasm Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Game.HandleAccept.Checkers (consInv)

theorem twoWords_instance : (Verify.instance? twoWords).isSome = true := by decide +kernel

/-- **`twoWords` meets the writer specification of `twoWordsL`** (no sentinel). -/
theorem twoWords_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf twoWords) (consInv twoWords)
      (writerISpec (consW (BitVec 64)) none (consWDecAsk twoIx) (consWDecAns twoIx) ρ twoWordsL)
      (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords.twoWords_sat P ρ

/-- **`twoWords` accepts only `(x x+1)`** (store semantics, no sentinel, no UB). -/
theorem twoWords_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleConsWLang P twoWords twoIx pol ⊆ twoWordsL :=
  consWLang_sound_of_gameSat (Inv := consInv twoWords) (fun ρ => hsen ▸ twoWords_sat P ρ) rfl rfl
    hw ha

/-- **`twoWords` accepts only `(x x+1)`** over any set of fixed environments (no sentinel). -/
theorem twoWords_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsWFixedLang P twoWords twoIx pol Envs ⊆ twoWordsL :=
  consWFixedLang_sound_of_gameSat (Inv := consInv twoWords) (fun ρ _ => hsen ▸ twoWords_sat P ρ)
    rfl rfl

end Silmaril.Wasm.Game.HandleAccept.Writers.Builders
