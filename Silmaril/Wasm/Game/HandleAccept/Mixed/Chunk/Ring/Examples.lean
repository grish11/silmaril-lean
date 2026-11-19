module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive

/-!
# A ring buffer in linear memory: a play built forwards (non-vacuity)

The session of **four export calls** `feed(7)`, `feed(8)`, `finish(1)`, `finish(1)`, the `k`-th
callout answered with the fresh handle `k + 1`: `feed(7)` stores `7` at bytes `[0, 8)` of the
memory page, `feed(8)` stores `8` at `[8, 16)`; the first `finish(1)` calls `nil() = 1`, loads
`7` from the start slot, calls `word(7) = 2`, `cons(2, 1) = 3`, advances the start slot and
answers `(1, 3)`, consuming **one** of the two buffered values; the second calls `nil() = 4`,
loads `8` from the new start slot, calls `word(8) = 5`, `cons(5, 4) = 6` and answers `(1, 6)`.

Kernel replay (as for `chunkTake`) does not finish on a 64 KiB page, so the play is built by
hand (`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive.ring_session`): the runs
between callouts are composed from Core `Step` rules with the store symbolic, the straight-line
code evaluated by `Silmaril.Wasm.Logic.Core.exec_sound`, the memory reasoned about with
`Memory.store`/`Memory.load` lemmas (`load_store_same`, `load_store_disjoint`), never evaluating
the page. Only the decoded moves (values and handles) are checked by kernel evaluation.

The play is built **for every capacity** `2 ≤ cap ≤ 8192` at once (the slot addresses are
computed from `cap` symbolically; two values must fit the buffer):

* `chunkRingN_relates_7`: the first `finish` relates `([7], (7))`;
* `chunkRingN_relates_8`: the second relates `([8], (8))`, the value left in memory;
* `chunkRingN_rel_eq_8`: with `chunkRingN_rel`, the relation restricted to the input `[8]` is
  exactly `{([8], (8))}`;
* `chunkRingN_relates_7_one`: the one-value session `feed(7)`, `finish(1)` relates `([7], (7))`
  for every capacity `1 ≤ cap ≤ 8192`; `chunkRing1_relates_7`, `chunkRing1_rel_eq_7`: the
  **one-slot** buffer `chunkRingN 1` (where `feed(7)` fills the buffer) relates `([7], (7))`,
  and at the input `[7]` only that;
* instances: `chunkRing_relates_7`, `chunkRing_relates_8`, `chunkRing_rel_eq_8` (eight slots),
  `chunkRing8192_relates_8`, `chunkRing8192_rel_eq_8` (8192 slots, the whole page).

**Profiles and policies.** Every profile (the steps used are profile-free), every writer policy
whose sentinel, if any, is `0`, and every parsing policy with sentinel `0`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

open Silmaril.Wasm Silmaril.Formats Silmaril.Accept.Handle Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Writers.Builders

/-! ## Every capacity from two to 8192 -/

section Positive

variable {cap : Nat} (h2 : 2 ≤ cap) (h8 : cap ≤ 8192) {P : Profile} {pol : Policy (BitVec 32)}
  (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
include h2 h8 hs h0

/-- **The first `finish(1)` consumes one of two values buffered in memory: `([7], (7))`**, for
every capacity `2 ≤ cap ≤ 8192`. -/
theorem chunkRingN_relates_7 :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive.chunkRingN_relates_7 h2 h8 hs h0

/-- **The second `finish(1)` consumes the value left in memory: `([8], (8))`**, for every
capacity `2 ≤ cap ≤ 8192`. -/
theorem chunkRingN_relates_8 :
    ([8], SExp2.ofAtoms [8]) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive.chunkRingN_relates_8 h2 h8 hs h0

end Positive

/-- **The relation at the input `[8]`** is exactly `([8], (8))`, for every capacity
`2 ≤ cap ≤ 8192`. -/
theorem chunkRingN_rel_eq_8 {cap : Nat} (h2 : 2 ≤ cap) (h8 : cap ≤ 8192) {P : Profile}
    {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    {t | ([8], t) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol} =
      {SExp2.ofAtoms [8]} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨chunkRingN_relates_8 h2 h8 (fun r h => by simp [hsen] at h) h0,
    fun _ => chunkRingN_rel ⟨by omega, h8⟩ P hsen hw ha hb ho⟩

/-! ## One value, and the one-slot buffer -/

/-- **One value, every capacity `1 ≤ cap ≤ 8192`**: `feed(7)`, `finish(1)` relates
`([7], (7))`. -/
theorem chunkRingN_relates_7_one {cap : Nat} (h1 : 1 ≤ cap) (h8 : cap ≤ 8192) {P : Profile}
    {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
    {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0) :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P (chunkRingN cap) twoIx ringPix pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.RingLive.chunkRingN_relates_7_one h1 h8 hs h0

/-- **The one-slot buffer relates `([7], (7))`.** -/
theorem chunkRing1_relates_7 {P : Profile} {pol : Policy (BitVec 32)}
    (hs : ∀ r, pol.sentinel = some r → r = 0) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P (chunkRingN 1) twoIx ringPix pol ppol :=
  chunkRingN_relates_7_one (by decide) (by decide) hs h0

/-- **The relation of the one-slot buffer at the input `[7]`** is exactly `([7], (7))`. -/
theorem chunkRing1_rel_eq_7 {P : Profile} {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    {t | ([7], t) ∈ moduleMixedRel P (chunkRingN 1) twoIx ringPix pol ppol} =
      {SExp2.ofAtoms [7]} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨chunkRing1_relates_7 (fun r h => by simp [hsen] at h) h0,
    fun _ => chunkRingN_rel ⟨by decide, by decide⟩ P hsen hw ha hb ho⟩

/-! ## Eight values, and a full page -/

section Eight

variable {P : Profile} {pol : Policy (BitVec 32)} (hs : ∀ r, pol.sentinel = some r → r = 0)
  {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0)
include hs h0

/-- **The first `finish(1)` consumes one of two values buffered in memory: `([7], (7))`.** -/
theorem chunkRing_relates_7 :
    ([7], SExp2.ofAtoms [7]) ∈ moduleMixedRel P chunkRing twoIx ringPix pol ppol :=
  chunkRingN_relates_7 (by decide) (by decide) hs h0

/-- **The second `finish(1)` consumes the value left in memory: `([8], (8))`.** -/
theorem chunkRing_relates_8 :
    ([8], SExp2.ofAtoms [8]) ∈ moduleMixedRel P chunkRing twoIx ringPix pol ppol :=
  chunkRingN_relates_8 (by decide) (by decide) hs h0

/-- With **8192 slots** (the buffer fills the whole page), the second `finish(1)` relates
`([8], (8))`. -/
theorem chunkRing8192_relates_8 :
    ([8], SExp2.ofAtoms [8]) ∈ moduleMixedRel P (chunkRingN 8192) twoIx ringPix pol ppol :=
  chunkRingN_relates_8 (by decide) (by decide) hs h0

end Eight

/-- **The relation at the input `[8]`** is exactly `([8], (8))`. -/
theorem chunkRing_rel_eq_8 {P : Profile} {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (h0 : ppol.sentinel = 0) (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    {t | ([8], t) ∈ moduleMixedRel P chunkRing twoIx ringPix pol ppol} = {SExp2.ofAtoms [8]} :=
  chunkRingN_rel_eq_8 (by decide) (by decide) hsen hw ha h0 hb ho

/-- **The relation of the 8192-slot buffer at the input `[8]`** is exactly `([8], (8))`. -/
theorem chunkRing8192_rel_eq_8 {P : Profile} {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    {ppol : PPolicy (BitVec 32)} (h0 : ppol.sentinel = 0) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) :
    {t | ([8], t) ∈ moduleMixedRel P (chunkRingN 8192) twoIx ringPix pol ppol} =
      {SExp2.ofAtoms [8]} :=
  chunkRingN_rel_eq_8 (by decide) (by decide) hsen hw ha h0 hb ho

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
