module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Defs
public import Silmaril.Wasm.Game.HandleAccept.Thms
public import Silmaril.Semantics.Accept.Handle.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.ReadPolicy.Module

/-!
# Non-trapping read policies at Wasm: laws

* `errD_disjoint`: the error answers `errD` are a typed error (`ErrorDisjoint`) for the cons
  reader: under `OnBadRead.dflt errD` an answer equal to the error code is exactly an invalid
  query (`Silmaril.Accept.Handle.error_iff_invalid`).
* `polLang_subset_of_AG`, **the policy bridge**: plays assume/guarantee correct for `polISpec`
  (answers *allowed* by the read policy in `ρ`) have their reader language under that policy
  included in `L`, for every read and accept policy other than `ub`: the trapping policy, typed
  errors (`dflt`) and arbitrary answers alike. What changes between policies is what a module
  can prove from an answer.
* `errLang_sound_of_gameSat`, `errLang_sound_of_forall`: the same from a module's Hoare-logic
  obligation, in one environment and over a set of environments.
* **`carCheck_sound`**: `carCheck` accepts only cons cells with an atom `car` (`carAtomL`),
  under the trapping policy and under the typed-error policy `dflt errD`, in every set of
  environments, every profile and every accept policy but `ub`. It is sound under `dflt`
  **because it checks the error code**: `car(h) = -1` is the only answer an invalid `car` query
  gets, and the module returns on it. `Examples` shows that `carNoCheck` (no check) is unsound
  under `dflt errD`, and `carCheck` unsound under `arbitrary`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.ReadPolicy

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Strategy (ISpec AG)
open Silmaril.Wasm.Logic.GameLink (GameSat)

theorem errD_disjoint : ErrorDisjoint (consR (BitVec 64) (BitVec 32)) errD :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy.errD_disjoint

variable {E F : Sig.{0}}

theorem polLang_subset_of_AG {Q A H X : Type} {R : Reader Q A H X} {pol : OnBadRead Q A}
    {oa : OnInvalid} {ρ : Silmaril.Accept.Handle.Env H X} {L : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (REv Q A H)} {dAns : (e : E.Op) → E.Ar e → Option (REv Q A H)}
    (hAG : ∀ p ∈ σ, AG (polISpec R pol dAsk dAns ρ L) (topISpec F) p)
    (hans : ∀ e v h, dAns e v ≠ some (.accept h)) (hp : pol ≠ .ub) (hoa : oa ≠ .ub) :
    readerLang R pol oa {ρ} (handleTraces σ (some .enter) dAsk dAns) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy.polLang_subset_of_AG hAG hans hp hoa

/-- **Soundness of a reader module with error codes** from its Hoare-logic obligation. -/
theorem errLang_sound_of_gameSat {P : Profile} {m : Module} {ix : ConsImports}
    {pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))} {oa : OnInvalid}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))}
    {L : Set (SExp2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : GameSat P (Verify.instOf m) Inv
      (polISpec (consR (BitVec 64) (BitVec 32)) pol (consDecAsk ix) (errDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hp : pol ≠ .ub) (hoa : oa ≠ .ub) :
    moduleErrLang P m ix pol oa {ρ} ⊆ L :=
  polLang_subset_of_AG (fun _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hp).2)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy.errDecAns_ne_accept ix) hp hoa

/-- Over a set of environments. -/
theorem errLang_sound_of_forall {P : Profile} {m : Module} {ix : ConsImports}
    {pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))} {oa : OnInvalid}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))}
    {L : Set (SExp2 (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv
      (polISpec (consR (BitVec 64) (BitVec 32)) pol (consDecAsk ix) (errDecAns ix) ρ L)
      (topISpec _))
    (hs : Inv (Verify.instOf m).store) (hp : pol ≠ .ub) (hoa : oa ≠ .ub) :
    moduleErrLang P m ix pol oa Envs ⊆ L := by
  intro x hx
  unfold moduleErrLang readerLang langOver at hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨⟨ρ, hρ⟩, hx⟩ := hx
  refine errLang_sound_of_gameSat (hm ρ hρ) hs hp hoa ?_
  unfold moduleErrLang readerLang langOver
  rw [Set.mem_iUnion]
  exact ⟨⟨ρ, rfl⟩, hx⟩

/-! ## `carCheck` -/

theorem carCheck_instance : (Verify.instance? carCheck).isSome = true := by decide +kernel
theorem carNoCheck_instance : (Verify.instance? carNoCheck).isSome = true := by decide +kernel

/-- **`carCheck` accepts only cons cells with an atom `car`** under the trapping and the
typed-error read policies (every set of environments, profile and accept policy but `ub`). -/
theorem carCheck_sound (P : Profile)
    {pol : OnBadRead (ConsQ (BitVec 32)) (ConsA (BitVec 64) (BitVec 32))}
    (hpol : pol = .trap ∨ pol = .dflt errD) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleErrLang P carCheck Checkers.consIx pol oa Envs ⊆ carAtomL :=
  errLang_sound_of_forall
    (fun ρ _ => Silmaril.Proofs.Wasm.Game.HandleAccept.ReadPolicy.carCheck_sat P hpol ρ) rfl
    (by rcases hpol with rfl | rfl <;> nofun) hoa

end Silmaril.Wasm.Game.HandleAccept.ReadPolicy
