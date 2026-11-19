module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Bridge
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Example

/-!
# Chunk exports in instance plays: what is proved

* **The chunk bridge** (`moduleMixedRel_sound_of_chunkSat`): for a module with cons writer imports
  `wix` and parsing exports `pix` (`feed`, `finish`, and any of the others), if in every
  environment `ρ` the instance meets the chunk specification
  `chunkSSpec pix ppol ρ R (Inv ρ)` under the writer import specification
  (`mixedISpec wix pol.sentinel ρ`), from a store representing the empty buffer, then the store
  relation of the module is in `R`, for writer and parsing policies without undefined
  behaviour. The ghost state of a play is the chunk buffer of the parsing host
  (`Silmaril.Wasm.Game.HandleAccept.Mixed.Stream.strategy_sag` with the assume/guarantee law
  along the chunk buffer, `Silmaril.Accept.Mixed.mixedRel_subset_of_chunkAG`), so
  `finish(n) -> (used, h)` is constrained by the `used` values after the cursor.
  `moduleMixedFixedRel_sound_of_chunkSat`: the same over fixed environments `Envs` (the
  obligation in every `ρ ∈ Envs`), for every writer policy (`mixedFixedRel_subset_of_chunkAG`).
* `chunkStack_instance`, `chunkInv_init`: the example validates, instantiates, and its
  instantiated store represents the empty buffer.
* **Stateful Hoare-logic specification** (`chunkStack_sat`): in every environment `ρ` and every
  profile, for every parsing policy, assuming writer answers agree with `ρ` (no writer sentinel),
  `chunkStack` meets `chunkSSpec chunkPix ppol ρ chunkR (chunkInv ρ)`.
* **Soundness** (`chunkStack_sound`, `chunkStack_rel`): for every profile, writer policy without
  a sentinel and without UB, and parsing policy without UB (any sentinel, any `doneClears`),
  every pair of `chunkStack` is `(vs, SExp2.ofAtoms vs.reverse)`: the values consumed by a
  `finish`, most recent first; a `finish` that consumes nothing relates `([], ())`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing

/-- **Soundness of a chunked parser module building its trees** (store semantics) from its
stateful Hoare-logic obligation in every environment. -/
theorem moduleMixedRel_sound_of_chunkSat {V : Type} {P : Profile} {m : Module}
    {wix : ConsWImports} {pix : ParseExports V} {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} {R : Set (List V × SExp2 (BitVec 64))}
    {Inv : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    (hm : ∀ ρ, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (chunkSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ, Inv ρ [] (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P m wix pix pol ppol ⊆ R :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.moduleMixedRel_sound_of_chunkSat hm hs hw ha
    hb ho

/-- **Soundness of a chunked parser module over fixed environments**, for every writer policy
(including sentinels and undefined behaviour of the writer). -/
theorem moduleMixedFixedRel_sound_of_chunkSat {V : Type} {P : Profile} {m : Module}
    {wix : ConsWImports} {pix : ParseExports V} {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} {R : Set (List V × SExp2 (BitVec 64))}
    {Inv : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)) → List V → Store Nat → Prop}
    {Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))}
    (hm : ∀ ρ ∈ Envs, SGameSat P (Verify.instOf m) (mixedISpec wix pol.sentinel ρ)
      (chunkSSpec pix ppol ρ R (Inv ρ)))
    (hs : ∀ ρ ∈ Envs, Inv ρ [] (Verify.instOf m).store) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedFixedRel P m wix pix pol ppol Envs ⊆ R :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.moduleMixedFixedRel_sound_of_chunkSat hm hs
    hb ho

theorem chunkStack_instance : (Verify.instance? chunkStack).isSome = true := by decide +kernel

theorem chunkInv_init (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    chunkInv ρ [] (Verify.instOf chunkStack).store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.chunkInv_init ρ

/-- **`chunkStack` meets its chunk specification.** -/
theorem chunkStack_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (Verify.instOf chunkStack) (mixedISpec twoIx none ρ)
      (chunkSSpec chunkPix ppol ρ chunkR (chunkInv ρ)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.chunkStack_sat P ρ ppol

/-- **`chunkStack` relates only `(vs, (vs reversed))`** (store semantics). -/
theorem chunkStack_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P chunkStack twoIx chunkPix pol ppol ⊆ chunkR :=
  moduleMixedRel_sound_of_chunkSat (Inv := chunkInv)
    (fun ρ => hsen ▸ chunkStack_sat P ρ ppol) chunkInv_init hw ha hb ho

/-- **`chunkStack` relates only `(vs, (vs reversed))` over fixed environments**, for every
writer policy without a sentinel. -/
theorem chunkStack_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    {ppol : PPolicy (BitVec 32)} (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleMixedFixedRel P chunkStack twoIx chunkPix pol ppol Envs ⊆ chunkR :=
  moduleMixedFixedRel_sound_of_chunkSat (Inv := chunkInv)
    (fun ρ _ => hsen ▸ chunkStack_sat P ρ ppol) (fun ρ _ => chunkInv_init ρ) hb ho

/-- Every related pair, read off. -/
theorem chunkStack_rel (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {w : List (BitVec 64)}
    {t : SExp2 (BitVec 64)} (h : (w, t) ∈ moduleMixedRel P chunkStack twoIx chunkPix pol ppol) :
    t = SExp2.ofAtoms w.reverse :=
  chunkStack_sound P hsen hw ha hb ho h

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
