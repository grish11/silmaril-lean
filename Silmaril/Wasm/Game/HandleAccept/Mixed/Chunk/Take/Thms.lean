module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take

/-!
# A chunked parser with partial consumption: soundness

* `chunkTake_instance`, `takeInv_init`: the example validates, instantiates, and its instantiated
  store represents the empty buffer.
* **Stateful Hoare-logic specification** (`chunkTake_sat`): in every environment `ρ` and every
  profile, for every parsing policy, assuming writer answers agree with `ρ` (no writer sentinel),
  `chunkTake` meets `chunkSSpec takePix ppol ρ takeR takeInv`: `finish(n)` with `0 < n ≤` the
  buffered count returns `(n, h)` with `h` denoting the list of the oldest `n` buffered values and
  leaves the rest buffered; otherwise it returns `(0, h)`, `h` denoting `()`.
* **Soundness** (`chunkTake_sound`, store semantics, writer policies without a sentinel or UB;
  `chunkTake_fixed_sound`, fixed environments, writer policies without a sentinel): every pair is
  `(vs, SExp2.ofAtoms vs)`, the values consumed by one `finish`, in order.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk

theorem chunkTake_instance : (Verify.instance? chunkTake).isSome = true := by decide +kernel

theorem takeInv_init : takeInv [] (Verify.instOf chunkTake).store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take.takeInv_init

/-- **`chunkTake` meets its chunk specification.** -/
theorem chunkTake_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (Verify.instOf chunkTake) (mixedISpec twoIx none ρ)
      (chunkSSpec takePix ppol ρ takeR takeInv) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take.chunkTake_sat P ρ ppol

/-- **`chunkTake` relates only `(vs, (vs))`** (store semantics). -/
theorem chunkTake_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P chunkTake twoIx takePix pol ppol ⊆ takeR :=
  moduleMixedRel_sound_of_chunkSat (Inv := fun _ => takeInv)
    (fun ρ => hsen ▸ chunkTake_sat P ρ ppol) (fun _ => takeInv_init) hw ha hb ho

/-- **`chunkTake` relates only `(vs, (vs))` over fixed environments**, for every writer policy
without a sentinel. -/
theorem chunkTake_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) {ppol : PPolicy (BitVec 32)} (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleMixedFixedRel P chunkTake twoIx takePix pol ppol Envs ⊆ takeR :=
  moduleMixedFixedRel_sound_of_chunkSat (Inv := fun _ => takeInv)
    (fun ρ _ => hsen ▸ chunkTake_sat P ρ ppol) (fun _ _ => takeInv_init) hb ho

/-- Every related pair, read off. -/
theorem chunkTake_rel (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {w : List (BitVec 64)}
    {t : SExp2 (BitVec 64)} (h : (w, t) ∈ moduleMixedRel P chunkTake twoIx takePix pol ppol) :
    t = SExp2.ofAtoms w :=
  chunkTake_sound P hsen hw ha hb ho h

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take
