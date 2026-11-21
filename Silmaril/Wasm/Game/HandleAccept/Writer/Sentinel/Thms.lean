module

public import Silmaril.Wasm.Game.HandleAccept.Writer.Sentinel.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Sentinel.Sat
import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.Sentinel.Fail

/-!
# Sentinel-testing writer modules: what is proved

* `twoWordsZ` and `twoWordsM` validate and instantiate (`twoWordsZ_instance`,
  `twoWordsM_instance`).
* **Hoare-logic specifications** (`twoWordsZ_sat`, `twoWordsM_sat`): in every fixed environment
  `ρ` and every profile, the instance meets the cons writer specification
  `writerISpec consW (some s) … ρ twoWordsL` **with the sentinel** `s = 0` (resp. `s = -1`):
  every answered write may return the sentinel, and the module tests every result before
  using it (proofs in `Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel`).
* **Soundness with the sentinel** (unlike `twoWords_sound`, which needs `pol.sentinel = none`):
  for every profile and every policy whose sentinel is `0` (resp. `-1`), the trees the module
  accepts are the lists `(x x+1)`: in the store semantics without UB (`twoWordsZ_sound`,
  `twoWordsM_sound`) and over any set of fixed environments, for every invalid-use policy
  (`twoWordsZ_fixed_sound`, `twoWordsM_fixed_sound`).
* **Failures accept nothing**: a trace of writes and export calls only (a run whose first write
  failed and which returned) accepts nothing under any policy without undefined writes
  (`accepts_writeOrEnter`).

The two modules are proved directly, from one generic body proof over the failure test
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel.sent_sat`); they are not related by
the handle swap of `Silmaril.Accept.Handle.writerLang_sentinel_swap`, which renames trace
values but not the module's own tests.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel

open Silmaril.Wasm Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Writers.Builders
open Silmaril.Wasm.Game.HandleAccept.Checkers (consInv)

theorem twoWordsZ_instance : (Verify.instance? twoWordsZ).isSome = true := by decide +kernel
theorem twoWordsM_instance : (Verify.instance? twoWordsM).isSome = true := by decide +kernel

/-- **`twoWordsZ` meets the writer specification of `twoWordsL` with the sentinel `0`.** -/
theorem twoWordsZ_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf twoWordsZ) (consInv twoWordsZ)
      (writerISpec (consW (BitVec 64)) (some 0) (consWDecAsk twoIx) (consWDecAns twoIx) ρ
        twoWordsL) (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel.twoWordsZ_sat P ρ

/-- **`twoWordsM` meets the writer specification of `twoWordsL` with the sentinel `-1`.** -/
theorem twoWordsM_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    Silmaril.Wasm.Logic.GameLink.GameSat P (Verify.instOf twoWordsM) (consInv twoWordsM)
      (writerISpec (consW (BitVec 64)) (some (-1)) (consWDecAsk twoIx) (consWDecAns twoIx) ρ
        twoWordsL) (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel.twoWordsM_sat P ρ

/-- **`twoWordsZ` accepts only `(x x+1)` with the sentinel `0`** (store semantics, no UB). -/
theorem twoWordsZ_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = some 0)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleConsWLang P twoWordsZ twoIx pol ⊆ twoWordsL :=
  consWLang_sound_of_gameSat (Inv := consInv twoWordsZ) (fun ρ => hsen ▸ twoWordsZ_sat P ρ)
    rfl rfl hw ha

/-- **`twoWordsM` accepts only `(x x+1)` with the sentinel `-1`** (store semantics, no UB). -/
theorem twoWordsM_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = some (-1)) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleConsWLang P twoWordsM twoIx pol ⊆ twoWordsL :=
  consWLang_sound_of_gameSat (Inv := consInv twoWordsM) (fun ρ => hsen ▸ twoWordsM_sat P ρ)
    rfl rfl hw ha

/-- **`twoWordsZ` accepts only `(x x+1)`** over any set of fixed environments (sentinel `0`,
every invalid-use policy). -/
theorem twoWordsZ_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = some 0)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsWFixedLang P twoWordsZ twoIx pol Envs ⊆ twoWordsL :=
  consWFixedLang_sound_of_gameSat (Inv := consInv twoWordsZ)
    (fun ρ _ => hsen ▸ twoWordsZ_sat P ρ) rfl rfl

/-- **`twoWordsM` accepts only `(x x+1)`** over any set of fixed environments (sentinel `-1`,
every invalid-use policy). -/
theorem twoWordsM_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = some (-1))
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleConsWFixedLang P twoWordsM twoIx pol Envs ⊆ twoWordsL :=
  consWFixedLang_sound_of_gameSat (Inv := consInv twoWordsM)
    (fun ρ _ => hsen ▸ twoWordsM_sat P ρ) rfl rfl

/-- **A trace of writes and export calls accepts nothing**, for every writer policy without
undefined writes. -/
theorem accepts_writeOrEnter {Op X H : Type} [DecidableEq H] {W : Writer Op X}
    {pol : Policy H} (hw : pol.onWrite ≠ .ub) {t : List (WEv Op H)}
    (ht : ∀ e ∈ t, writeOrEnter e = true) : (writer W pol).accepts t = ∅ :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel.accepts_writeOrEnter hw ht

end Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel
