module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMixStale

/-!
# Memory mixed sessions: `blobEcho`

For every profile, against every host admitted by `blobReply` (keeps the code, never shrinks
memory `0`, may rewrite it, may trap or throw; `read` returns at most its `cap`), in the store
semantics of `Silmaril.Accept.Mixed` (a handle returned by `finish` resolves in the store of the
trees the module wrote):

* `blobEcho_len` (**soundness, length only**): for writer policies without undefined behaviour,
  parsing policies without undefined behaviour, and a writer sentinel that is absent or the
  parser's, every related pair `(w, x)` has `w` of at most `16` bytes and `x` a byte atom of
  **the same length** as `w` (`lenRel`). Proof: a Hoare-logic proof that every
  `finish(n, h)` call has `n ≤ 16` and `h` the sentinel or a handle denoting, in the writer store
  `σ`, a byte atom of `n` bytes, assuming every decoded write agrees with `σ`
  (`Silmaril.Accept.Mixed.WriteAgrees`); the bridge `tagTraces_pre`; and the store-semantics
  assume/guarantee law `Silmaril.Accept.Mixed.mixedRel_subset_of_AG` (the witness `σ` is the
  final store of the run).
* `blobEcho_live` (**non-vacuity**): `(68 69, bytes 68 69)` is related (the session against
  `blobEnv q`).
* `blobEcho_stale`, `blobEcho_not_exact` (**the stale-chunk hazard, a regression**): against
  `staleEnv q`, which traps the first `blob` call after answering `read`, the chunk `68 69`
  stays buffered, and the second invocation's `finish(2, q)` consumes it while `q` denotes the
  new chunk `69 68`: `(68 69, bytes 69 68)` is related, so the relation is **not** included in
  the exact relation `exactRel`.

**What is not proved.** Exact content (`w` equals the bytes of `x`) does not hold for the
admitted hosts (`blobEcho_not_exact`). For hosts that never trap `blob` it is expected, but it
relates three events of one invocation (the chunk read, the bytes `blob` observes, the handle
`finish` reports): the per-call contracts of `MemContract` constrain each callout on its own,
and `tagTraces_pre` gives no order or multiplicity of the calls of an invocation, so a proof
needs a history-sensitive bridge: see `Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost`
(ghost state in host codes) and the exact, stale-chunk-safe `drainEcho`
(`Silmaril.Wasm.Game.HandleAccept.MemSound.Exact`, `drainEcho_exact`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix

open Silmaril.Wasm Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Formats

/-- **Every pair `blobEcho` relates is in the length relation.** -/
theorem blobEcho_len (P : Profile) {pol : Policy (BitVec 32)} {ppol : PPolicy (BitVec 32)}
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) (hs : pol.sentinel = none ∨ pol.sentinel = some ppol.sentinel) :
    memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol ⊆ lenRel :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix.blobEcho_len P hw ha hb ho hs

/-- **`blobEcho` relates `68 69` to the byte atom `68 69`.** -/
theorem blobEcho_live (P : Profile) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))
    {q : BitVec 32} (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q) :
    (([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix.be_live P pol ppol hq hpq

/-- **The stale pair**: `blobEcho` relates `68 69` to the byte atom `69 68`. -/
theorem blobEcho_stale (P : Profile) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))
    {q : BitVec 32} (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q) :
    (([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix.be_stale P pol ppol hq hpq

/-- **`blobEcho` is not exact** against the admitted hosts. -/
theorem blobEcho_not_exact (P : Profile) (pol : Policy (BitVec 32)) (ppol : PPolicy (BitVec 32))
    {q : BitVec 32} (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q) :
    ¬ memMixedRel P (ReplyEnvs blobReply) 0 blobEcho {} {} pol ppol ⊆ exactRel :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullMix.be_not_exact P pol ppol hq hpq

end Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix
