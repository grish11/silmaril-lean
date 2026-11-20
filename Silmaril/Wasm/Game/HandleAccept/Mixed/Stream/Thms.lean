module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Thms
public import Silmaril.Semantics.Accept.Mixed.Stream.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.Bridge

/-!
# Streaming parsers that build their trees: the stateful assume/guarantee bridge

* **The game link for stateful specifications** (`strategy_sag`): if the instance meets the
  stateful specification `S` under `Ii` (`SGameSat P I Ii S`), every play of its strategy from a
  store representing the ghost state `g` is assume/guarantee correct read from `g`
  (`SAG Ii S g`). This is `Silmaril.Wasm.Logic.GameLink.strategy_sound` with the store invariant
  indexed by a ghost state that moves at every export answer.
* **Streaming soundness** (`moduleMixedRel_sound_of_streamSat`): for a module with cons writer
  imports `wix` and parsing exports `pix` (any of `parse`, `append`, `done`, …), if in every
  environment `ρ` the obligation

  `SGameSat P (instOf m) (mixedISpec wix pol.sentinel ρ) (streamSSpec pix ppol ρ R (Inv ρ))`

  holds and the instantiated store represents the empty buffer (`Inv ρ []`), the store relation
  is in `R`, for writer and parsing policies without undefined behaviour. The ghost state of a
  play is the parsing host's append buffer, so `done() -> h` is constrained by the values
  appended since the last `done` (`Silmaril.Accept.Mixed.mixedRel_subset_of_streamAG`).
  `moduleMixedFixedRel_sound_of_streamSat`: the same over fixed environments, for every writer
  policy.

Compared with `moduleMixedRel_sound_of_gameSat` (one-shot exports only, `ReturnsIn` constrains
each answer on its own), the export specification may depend on the history of the session
through the store invariant.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Stream

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Parsing
  Silmaril.Wasm.Game.HandleAccept.Mixed
open Silmaril.Wasm.Logic.Strategy (ISpec)

/-- **The game link for stateful specifications.** -/
theorem strategy_sag {I : ScalarInstance} {P : Profile} {G : Type} {Ii : ISpec I.E}
    {S : SSpec I G} (hm : SGameSat P I Ii S) {g : G} {s : Store Nat} (hs : S.inv g s)
    {p : List (Move I.E I.F)} (hp : p ∈ I.strategy P s) : SAG Ii S g p :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.strategy_sag hm hs hp

variable {V : Type} {P : Profile} {m : Module} {wix : ConsWImports} {pix : ParseExports V}
  {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)} {R : Set (List V × SExp2 (BitVec 64))}

/-- **Soundness of a streaming parser module building its trees** (store semantics) from its
stateful Hoare-logic obligation in every environment. -/
theorem moduleMixedRel_sound_of_streamSat
    {Inv : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    (hm : ∀ ρ, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (streamSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ, Inv ρ [] (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P m wix pix pol ppol ⊆ R :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.moduleMixedRel_sound_of_streamSat hm hs hw
    ha hb ho

/-- **Streaming soundness over fixed environments**, for every writer policy. -/
theorem moduleMixedFixedRel_sound_of_streamSat
    {Inv : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))}
    (hm : ∀ ρ ∈ Envs, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (streamSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ ∈ Envs, Inv ρ [] (Verify.instOf m).store) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedFixedRel P m wix pix pol ppol Envs ⊆ R :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Stream.moduleMixedFixedRel_sound_of_streamSat hm hs
    hb ho

end Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
