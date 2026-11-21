module

public import Silmaril.Wasm.Game.HandleAccept.Combined.Defs
public import Silmaril.Wasm.Game.HandleAccept.Thms
public import Silmaril.Semantics.Accept.Handle.Thms
public import Silmaril.Formats.SExp.Api.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.Module

/-!
# Combined writer and reader sessions of core Wasm modules: laws

* `crun_facts_init` (generic, any writer and monotone reader): along a run of the combined host
  from the empty store (no UB, trapping reads), the **final store** `ρ` leaves the sentinel
  undefined, every answered write of the run returns the sentinel or a handle denoting in `ρ`
  the tree built in `ρ`, every read is correct in `ρ`, and every accepted tree is the meaning in
  `ρ` of a handle passed to `accept` (or `accept_err` answered `true`), or, for `acceptAll` and
  kept batches, a tree built in `ρ` by a write of the run. Reads are answered from the store at
  the time of the read; monotonicity (`Reader.Mono`) carries them to the final store.
* `combLang_subset_of_AG`, **the combined store bridge**: if every play of a strategy is
  assume/guarantee correct for `combISpec W R pol.sentinel dAsk dAns ρ L` in every environment
  `ρ` leaving the sentinel undefined, its combined language is included in `L`. Only the final
  store of each run is used as `ρ`.
* `combLang_sound_of_gameSat`: the same from the Hoare-logic obligation `GameSat` of a module
  through the combined cons decoders.
* **`readBack_sound`**: the module `readBack` (write `cons(word(x), nil())`, read it back with
  `kind`, `car`, `cdr`, accept it only if the reads confirm the shape) accepts only one-element
  lists of words, `singleL`, for every profile and every writer policy without UB, **any
  sentinel included**: its Hoare proof uses only the read answers.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Combined

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Strategy (ISpec AG)
open Silmaril.Wasm.Logic.GameLink (GameSat)

theorem crun_facts_init {Op Q A X H : Type} [DecidableEq H] {W : Writer Op X}
    {R : Reader Q A H X} {pol : Policy H} (hM : R.Mono) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) {s' : WState H X} {t : List (CEv Op H Q A)} {S : Set X}
    (hr : (combined W R pol .trap).Run WState.init t s' S) :
    (∀ r, pol.sentinel = some r → s'.store r = none) ∧
      (∀ op args r, CEv.w (.write op args r) ∈ t →
        pol.sentinel = some r ∨ ∃ y, W.built s'.store op args = some y ∧ s'.store r = some y) ∧
      (∀ q a, CEv.r q a ∈ t → R.valid s'.store q ∧ R.ok s'.store q a) ∧
      (∀ x ∈ S, (∃ h, (CEv.w (.accept h) ∈ t ∨ CEv.w (.acceptErr h true) ∈ t) ∧
          s'.store h = some x) ∨
        ((CEv.w .acceptAll ∈ t ∨ CEv.w (.acceptBatch true) ∈ t) ∧
          ∃ op args r, CEv.w (.write op args r) ∈ t ∧ W.built s'.store op args = some x)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.crun_facts_init hM hw ha hr

variable {E F : Sig.{0}}

theorem combLang_subset_of_AG {X Op Q A : Type} {W : Writer Op X}
    {R : Reader Q A (BitVec 32) X} {pol : Policy (BitVec 32)} {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (CEv Op (BitVec 32) Q A)}
    {dAns : (e : E.Op) → E.Ar e → Option (CEv Op (BitVec 32) Q A)}
    (hAG : ∀ ρ : Silmaril.Accept.Handle.Env (BitVec 32) X,
      (∀ r, pol.sentinel = some r → ρ r = none) →
      ∀ p ∈ σ, AG (combISpec W R pol.sentinel dAsk dAns ρ L) (topISpec F) p)
    (hask : ∀ e ev, dAsk e = some ev → ∃ h, ev = .w (.accept h))
    (hans : ∀ e v ev, dAns e v = some ev →
      (∃ op args r, ev = .w (.write op args r)) ∨ ∃ q a, ev = .r q a)
    (hM : R.Mono) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    (combined W R pol .trap).lang (handleTraces σ (some (.w .enter)) dAsk dAns) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.combLang_subset_of_AG hAG hask hans hM hw ha

/-- **Soundness of a combined cons module** from its Hoare-logic obligation in every
environment leaving the sentinel undefined. -/
theorem combLang_sound_of_gameSat {P : Profile} {m : Module} {ix : CombImports}
    {pol : Policy (BitVec 32)} {L : Set (SExp2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)),
      (∀ r, pol.sentinel = some r → ρ r = none) →
      GameSat P (Verify.instOf m) Inv
        (combISpec (consW (BitVec 64)) (consR (BitVec 64) (BitVec 32)) pol.sentinel
          (combDecAsk ix) (combDecAns ix) ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleCombLang P m ix pol ⊆ L :=
  combLang_subset_of_AG
    (fun ρ hρ _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound (hm ρ hρ) hs hp).2)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.combDecAsk_isAccept ix)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.combDecAns_cases ix) consR_mono hw ha

/-! ## `readBack` -/

theorem readBack_instance : (Verify.instance? readBack).isSome = true := by decide +kernel

/-- **`readBack` meets the combined specification of `singleL`** in every fixed environment,
for every sentinel and profile (proof in
`Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.Module`). -/
theorem readBack_sat (P : Profile) (sn : Option (BitVec 32))
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf readBack) readBackInv
      (combISpec (consW (BitVec 64)) (consR (BitVec 64) (BitVec 32)) sn
        (combDecAsk readBackIx) (combDecAns readBackIx) ρ singleL) (topISpec _) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Combined.readBack_sat P sn ρ

/-- **`readBack` accepts only one-element lists of words**, in the combined store semantics
(reads answered from the current store, trapping when invalid), for every profile and every
writer policy without UB, with or without a failure sentinel. -/
theorem readBack_sound (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : moduleCombLang P readBack readBackIx pol ⊆ singleL :=
  combLang_sound_of_gameSat (fun ρ _ => readBack_sat P pol.sentinel ρ) rfl hw ha

end Silmaril.Wasm.Game.HandleAccept.Combined
