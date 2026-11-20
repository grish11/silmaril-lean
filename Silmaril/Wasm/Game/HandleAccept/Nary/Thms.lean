module

public import Silmaril.Wasm.Game.HandleAccept.Nary.Defs
public import Silmaril.Wasm.Game.HandleAccept.Thms
import Silmaril.Semantics.Accept.Host.Thms

/-!
# The n-ary S-expression reader API of core Wasm modules: laws

* `sxDecAns_ne_accept`: answers never decode to `accept` (they are read events by construction);
* `sexpLang_sound_of_gameSat`: the Hoare-logic obligation
  `GameSat P (instOf m) Inv (sexpISpec ix ρ L) (topISpec _)` (with a store invariant holding
  initially) gives `moduleSExpLang P m ix .trap oa {ρ} ⊆ L` for every accept policy without UB,
  through the generic bridge `readerLang_subset_of_AG` and
  `Silmaril.Wasm.Logic.GameLink.strategy_sound`; `sexpLang_sound_of_forall` for every
  environment of a set.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Nary

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.GameLink (GameSat)

theorem sxDecAns_ne_accept {ts : List FnType} (ix : SxRImports) (e : (ifaceSig ts).Op)
    (v : (ifaceSig ts).Ar e) (h : BitVec 32) : sxDecAns ix e v ≠ some (.accept h) := by
  unfold sxDecAns
  cases sxDecRead ix e v <;> simp

/-- **Soundness of an n-ary reader checker from its Hoare-logic obligation.** -/
theorem sexpLang_sound_of_gameSat {P : Profile} {m : Module} {ix : SxRImports}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))} {L : Set (SExp (BitVec 64))}
    {Inv : Store Nat → Prop}
    (hm : GameSat P (Verify.instOf m) Inv (sexpISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleSExpLang P m ix .trap oa {ρ} ⊆ L :=
  readerLang_subset_of_AG
    (fun _ hp => (Silmaril.Wasm.Logic.GameLink.strategy_sound hm hs hp).2)
    (fun _ _ h => h) (fun _ h hd hpre => hpre h hd)
    (sxDecAns_ne_accept ix) hoa

/-- For every environment of a set. -/
theorem sexpLang_sound_of_forall {P : Profile} {m : Module} {ix : SxRImports}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64)))}
    {L : Set (SExp (BitVec 64))} {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv (sexpISpec ix ρ L) (topISpec _))
    (hs : Inv (Verify.instOf m).store) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    moduleSExpLang P m ix .trap oa Envs ⊆ L := fun _ hx => by
  obtain ⟨⟨ρ, hρ⟩, hx⟩ := Silmaril.Accept.mem_langOver.1 hx
  exact sexpLang_sound_of_gameSat (hm ρ hρ) hs hoa (Silmaril.Accept.mem_langOver.2 ⟨⟨ρ, rfl⟩, hx⟩)

end Silmaril.Wasm.Game.HandleAccept.Nary
