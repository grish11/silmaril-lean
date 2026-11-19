module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.OnePoint

/-!
# Memory-observing soundness with ghost state: the bridge

* `gConfig_erase` (**the ghost is not observable**): erasing the ghost from the host code of a
  relabelled configuration gives the real configuration back; the relabelling changes nothing
  else, and host-free steps commute with it (`Silmaril.Proofs.Wasm.Component.Reference.Step.mapH`).
* `tagTraces_gpre` (**the ghost bridge**): for a module meeting the ghost obligation
  `GMemSat P m memIdx R K Inv g₀`, in every traced session against every environment whose
  replies `K.reply` admits (the environments of `ReplyEnvs K.reply`, unchanged by the ghost),
  every decoded input `x` whose earlier inputs all meet `K.ans` is

  - decoded at a call `o` (`R.callIn o = some x`) with `K.pre (tagGhost K.upd g₀ u) o`, where
    `u` is the tag prefix before `x`: **the guarantee at a call may depend on the decoded
    history** through the ghost of the prefix; or
  - decoded at the answer of a call `o` meeting `K.pre` in some ghost.

  The proof relates the real session to the relabelled configurations step by step: host-free
  steps by `Step.mapH`, a call redex of the real store to the redex of the relabelled store with
  host code `(h, g)`, an admitted answer to a step of `gHost` that moves the ghost over the decoded
  inputs, an invocation to the invocation of the relabelled store.
* `memSat_iff_gMemSat` (**the one-point case**): `MemSat` is `GMemSat` for the one-point ghost
  contract `K.toG` (ghost `Unit`, guarantee `fun _ => K.pre`) and invariant `fun _ => Inv`; and
  `tagTraces_pre_of_gpre`: the conclusion of the memory bridge
  `Silmaril.Wasm.Game.HandleAccept.MemSound.tagTraces_pre` follows from `tagTraces_gpre` through
  it, so the ghost bridge generalises the memory bridge.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Accept.IO Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Proofs.Wasm.Component.Reference (Config.mapH)

variable {X I O C G : Type}

/-- **The ghost is not observable**: erasing it gives the real configuration back. -/
theorem gConfig_erase (g : G) (c : Config Nat) : Config.mapH Prod.fst (gConfig g c) = c :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost.gConfig_erase g c

/-- The ghost of a concatenation. -/
theorem tagGhost_append (upd : G → I → G) (g : G) (ts us : List (Tag X I O C)) :
    tagGhost upd g (ts ++ us) = tagGhost upd (tagGhost upd g ts) us :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost.tagGhost_append upd g ts us

/-- **The ghost bridge.** -/
theorem tagTraces_gpre {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}
    {m : Module} {R : Roles X I O C} {K : GContract I G} {Inv : G → Store Nat → Prop} {g₀ : G}
    (hsat : GMemSat P m memIdx R K Inv g₀) (hE : ∀ s L, Envs s L → ReplyEnvs K.reply s L)
    {ts : List (Tag X I O C)} (hts : ts ∈ tagTraces P Envs memIdx m R)
    {u v : List (Tag X I O C)} {x : I} (hd : ts = u ++ .inp x :: v)
    (hu : ∀ y, Tag.inp y ∈ u → K.ans y) :
    ∃ o, (R.callIn o = some x ∧ K.pre (tagGhost K.upd g₀ u) o) ∨
      (∃ w, R.answerIn o w = some x ∧ ∃ g, K.pre g o) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost.tagTraces_gpre hsat hE hts hd hu

/-- **`MemSat` is the one-point case of `GMemSat`.** -/
theorem memSat_iff_gMemSat {P : Profile} {m : Module} {memIdx : Nat} {R : Roles X I O C}
    {K : MemContract I} {Inv : Store Nat → Prop} :
    MemSat P m memIdx R K Inv ↔ GMemSat P m memIdx R K.toG (fun _ => Inv) () :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Ghost.memSat_iff_gMemSat

/-- **The memory bridge from the ghost bridge**: the conclusion of `MemSound.tagTraces_pre`,
derived from `tagTraces_gpre` at the one-point ghost. -/
theorem tagTraces_pre_of_gpre {P : Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat}
    {m : Module} {R : Roles X I O C} {K : MemContract I} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx R K Inv) (hE : ∀ s L, Envs s L → ReplyEnvs K.reply s L)
    {ts : List (Tag X I O C)} (hts : ts ∈ tagTraces P Envs memIdx m R)
    {u v : List (Tag X I O C)} {x : I} (hd : ts = u ++ .inp x :: v)
    (hu : ∀ y, Tag.inp y ∈ u → K.ans y) :
    ∃ o, K.pre o ∧ (R.callIn o = some x ∨ ∃ w, R.answerIn o w = some x) :=
  match tagTraces_gpre (K := K.toG) (memSat_iff_gMemSat.1 hsat) hE hts hd hu with
  | ⟨o, .inl ⟨hc, hp⟩⟩ => ⟨o, hp, .inl hc⟩
  | ⟨o, .inr ⟨w, hw, _, hp⟩⟩ => ⟨o, hp, .inr ⟨w, hw⟩⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost
