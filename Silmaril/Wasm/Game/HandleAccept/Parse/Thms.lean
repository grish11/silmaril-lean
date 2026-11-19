module

public import Silmaril.Wasm.Game.HandleAccept.Parse.Defs
public import Silmaril.Semantics.Accept.Parse.Thms
public import Silmaril.Wasm.Logic.GameLink.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Parse.Basic

/-!
# Parsing exports of core Wasm modules: laws

* `toNat_of_usedOfI32`: the unsigned reading of `used` agrees with
  `Silmaril.Accept.Parse.usedOfI32` wherever that one is defined;
* `parseRel_oneShot` (generic): without UB on unresolved handles, every pair of the relation
  of `parse`/`reset`-only traces in a fixed environment `ρ` is `([v], x)` for a `parse(v)` event
  answered with a non-sentinel handle denoting `x` in `ρ`;
* `moduleParseRel_input_oneShot`: a module with only one-shot exports (`ParseExports.OneShot`)
  relates only one-value inputs, for every module, profile and environment set, with no
  obligation;
* `moduleParseRel_sound_of_gameSat`: the export-side bridge: the Hoare-logic obligation
  `GameSat P (instOf m) Inv (topISpec _) (parseESpec ix pol.sentinel ρ R)` gives
  `moduleParseRel P m ix pol {ρ} ⊆ R` for one-shot parsers (`…_of_forall` for a set of
  environments). Export answers are Proponent moves, so here the module *guarantees* the
  specification (`Silmaril.Wasm.Logic.GameLink.strategy_sound`) instead of assuming it.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Parsing

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Wasm.Game.HandleAccept
open Silmaril.Wasm.Logic.GameLink (GameSat)

theorem toNat_of_usedOfI32 {b : BitVec 32} {n : Nat} (h : usedOfI32 b = some n) :
    n = b.toNat := by
  unfold usedOfI32 at h
  split_ifs at h
  exact (Option.some.inj h).symm

theorem parseRel_oneShot {V H X : Type} [DecidableEq H] {pol : PPolicy H}
    (hb : pol.onBadHandle ≠ .ub) {ρ : Silmaril.Accept.Handle.Env H X} {T : Set (List (PEv V H))}
    (hT : ∀ t ∈ T, ∀ e ∈ t, (∃ w h, e = .parse w h) ∨ e = .reset) :
    ∀ q ∈ parseRel pol {ρ} T, ∃ t ∈ T, ∃ w h, PEv.parse w h ∈ t ∧ h ≠ pol.sentinel ∧
      ρ h = some q.2 ∧ q.1 = [w] :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.parseRel_oneShot hb hT

/-- A pair of the relation over `Envs` is a pair of the relation of one of them. -/
theorem mem_parseRel_envs {V H X : Type} [DecidableEq H] {pol : PPolicy H}
    {Envs : Set (Silmaril.Accept.Handle.Env H X)} {T : Set (List (PEv V H))} {q : List V × X}
    (hq : q ∈ parseRel pol Envs T) : ∃ ρ ∈ Envs, q ∈ parseRel pol {ρ} T :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.mem_parseRel_envs hq

/-- **One-shot parser modules relate only one-value inputs** (every module, profile and
environment set; no obligation). -/
theorem moduleParseRel_input_oneShot {V X : Type} {P : Profile} {m : Module}
    {ix : ParseExports V} {pol : PPolicy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)} (h1 : ix.OneShot)
    (hb : pol.onBadHandle ≠ .ub) :
    inputLang (moduleParseRel P m ix pol Envs) ⊆ {w | ∃ v, w = [v]} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.moduleParseRel_input_oneShot h1 hb

/-- **Soundness of a one-shot parser module from its Hoare-logic obligation.** -/
theorem moduleParseRel_sound_of_gameSat {V X : Type} {P : Profile} {m : Module}
    {ix : ParseExports V} {pol : PPolicy (BitVec 32)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) X} {R : Set (List V × X)} {Inv : Store Nat → Prop}
    (hm : GameSat P (Verify.instOf m) Inv (topISpec _) (parseESpec ix pol.sentinel ρ R))
    (hs : Inv (Verify.instOf m).store) (h1 : ix.OneShot) (hb : pol.onBadHandle ≠ .ub) :
    moduleParseRel P m ix pol {ρ} ⊆ R :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Parsing.moduleParseRel_sound_of_gameSat hm hs h1 hb

/-- For every environment of a set. -/
theorem moduleParseRel_sound_of_forall {V X : Type} {P : Profile} {m : Module}
    {ix : ParseExports V} {pol : PPolicy (BitVec 32)}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)} {R : Set (List V × X)}
    {Inv : Store Nat → Prop}
    (hm : ∀ ρ ∈ Envs, GameSat P (Verify.instOf m) Inv (topISpec _) (parseESpec ix pol.sentinel ρ R))
    (hs : Inv (Verify.instOf m).store) (h1 : ix.OneShot) (hb : pol.onBadHandle ≠ .ub) :
    moduleParseRel P m ix pol Envs ⊆ R := by
  intro q hq
  obtain ⟨ρ, hρ, hq⟩ := mem_parseRel_envs hq
  exact moduleParseRel_sound_of_gameSat (hm ρ hρ) hs h1 hb hq

end Silmaril.Wasm.Game.HandleAccept.Parsing
