module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

/-!
# A chunked parser with a ring buffer in linear memory: soundness

Every statement is proved **for every capacity** `cap` with `RingCap cap` (`0 < cap ≤ 8192`,
the buffer within the one page) by one proof generic in `cap` (`chunkRingN_*`), and restated for
the eight-value `chunkRing` (`chunkRing_*`, `ringCap_8`).

* `chunkRingN_instance`, `ringInv_initN`: the module validates, instantiates (for every `cap`,
  by kernel evaluation with `cap` free), and its instantiated store represents the empty buffer.
* **Stateful Hoare-logic specification** (`chunkRingN_sat`): in every environment `ρ` and every
  profile, for every parsing policy, assuming writer answers agree with `ρ` (no writer sentinel),
  `chunkRingN cap` meets `chunkSSpec ringPix ppol ρ takeR (ringInv cap)`: the store invariant
  `ringInv cap` reads the chunk buffer (up to `cap` values) off the two globals and the `i64`
  slots of linear memory; `finish(n)` with `0 < n ≤` the buffered count returns `(n, h)` with `h` denoting the
  list of the oldest `n` buffered values and leaves the rest buffered; otherwise it returns
  `(0, h)`, `h` denoting `()`.
* **Soundness** (`chunkRingN_sound`, store semantics, writer policies without a sentinel or UB;
  `chunkRingN_fixed_sound`, fixed environments, writer policies without a sentinel): every pair is
  `(vs, SExp2.ofAtoms vs)`, the values consumed by one `finish`, in order (`chunkRingN_rel`).

Non-vacuity is in `Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Examples`
(`chunkRingN_relates_7`, `chunkRingN_relates_8`, `chunkRingN_rel_eq_8`, for every
`2 ≤ cap ≤ 8192`; `chunkRingN_relates_7_one` for every `1 ≤ cap ≤ 8192`, and
`chunkRing1_relates_7`, `chunkRing1_rel_eq_7` for the one-slot buffer), by a play built forwards:
the replay used for `chunkTake`
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.mem_moduleMixedRel_of_replaySeqC`, by kernel
evaluation of the interpreter) does not scale to a module with a memory page: a single
`i64.store` followed by a load on a 65536-byte `ByteArray` does not finish in kernel evaluation
within ten minutes (the byte array is a list in the kernel, and `ByteArray.copySlice` rebuilds
it element by element).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take

/-! ## Every capacity -/

section Cap

variable {cap : Nat}

theorem chunkRingN_instance (cap : Nat) : (Verify.instance? (chunkRingN cap)).isSome = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.chunkRingN_instance cap

theorem ringInv_initN (hc : RingCap cap) : ringInv cap [] (Verify.instOf (chunkRingN cap)).store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.ringInv_init hc

/-- **`chunkRingN cap` meets its chunk specification**, for every capacity `0 < cap ≤ 8192`. -/
theorem chunkRingN_sat (hc : RingCap cap) (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (Verify.instOf (chunkRingN cap)) (mixedISpec twoIx none ρ)
      (chunkSSpec ringPix ppol ρ takeR (ringInv cap)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.chunkRingN_satI hc P ρ ppol

/-- **`chunkRingN cap` relates only `(vs, (vs))`** (store semantics). -/
theorem chunkRingN_sound (hc : RingCap cap) (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    {ppol : PPolicy (BitVec 32)} (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol ⊆ takeR :=
  moduleMixedRel_sound_of_chunkSat (Inv := fun _ => ringInv cap)
    (fun ρ => hsen ▸ chunkRingN_sat hc P ρ ppol) (fun _ => ringInv_initN hc) hw ha hb ho

/-- **`chunkRingN cap` relates only `(vs, (vs))` over fixed environments**, for every writer
policy without a sentinel. -/
theorem chunkRingN_fixed_sound (hc : RingCap cap) (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) {ppol : PPolicy (BitVec 32)} (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleMixedFixedRel P (chunkRingN cap) twoIx ringPix pol ppol Envs ⊆ takeR :=
  moduleMixedFixedRel_sound_of_chunkSat (Inv := fun _ => ringInv cap)
    (fun ρ _ => hsen ▸ chunkRingN_sat hc P ρ ppol) (fun _ _ => ringInv_initN hc) hb ho

/-- Every related pair, read off. -/
theorem chunkRingN_rel (hc : RingCap cap) (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    {ppol : PPolicy (BitVec 32)} (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub)
    {w : List (BitVec 64)} {t : SExp2 (BitVec 64)}
    (h : (w, t) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol) :
    t = SExp2.ofAtoms w :=
  chunkRingN_sound hc P hsen hw ha hb ho h

end Cap

/-! ## Eight values -/

theorem ringCap_8 : RingCap 8 := ⟨by decide, by decide⟩

theorem chunkRing_instance : (Verify.instance? chunkRing).isSome = true := chunkRingN_instance 8

theorem ringInv_init : ringInv 8 [] (Verify.instOf chunkRing).store := ringInv_initN ringCap_8

/-- **`chunkRing` meets its chunk specification.** -/
theorem chunkRing_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (Verify.instOf chunkRing) (mixedISpec twoIx none ρ)
      (chunkSSpec ringPix ppol ρ takeR (ringInv 8)) :=
  chunkRingN_sat ringCap_8 P ρ ppol

/-- **`chunkRing` relates only `(vs, (vs))`** (store semantics). -/
theorem chunkRing_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P chunkRing twoIx ringPix pol ppol ⊆ takeR :=
  chunkRingN_sound ringCap_8 P hsen hw ha hb ho

/-- **`chunkRing` relates only `(vs, (vs))` over fixed environments**, for every writer policy
without a sentinel. -/
theorem chunkRing_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) {ppol : PPolicy (BitVec 32)} (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleMixedFixedRel P chunkRing twoIx ringPix pol ppol Envs ⊆ takeR :=
  chunkRingN_fixed_sound ringCap_8 P hsen hb ho Envs

/-- Every related pair, read off. -/
theorem chunkRing_rel (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {w : List (BitVec 64)}
    {t : SExp2 (BitVec 64)} (h : (w, t) ∈ moduleMixedRel P chunkRing twoIx ringPix pol ppol) :
    t = SExp2.ofAtoms w :=
  chunkRing_sound P hsen hw ha hb ho h

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
