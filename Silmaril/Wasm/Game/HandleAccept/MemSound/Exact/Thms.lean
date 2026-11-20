module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Exact.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ExactReplay

/-!
# Exact pull-chunk echo: `drainEcho`

For every profile, against every host admitted by `blobReply` (the hosts of `blobEcho`: they keep
the code, never shrink memory `0`, may rewrite every global and the whole memory, may trap or
throw at every call; `read` returns at most its `cap`), in the store semantics of
`Silmaril.Accept.Mixed`, with the parser's sentinel `z` hardcoded in the module (**every** `z : BitVec 32`: the
instantiation shape `deOk z` and the spec instance are kernel evaluations with `z` free,
`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.deOk_all`, `deSpec_all`):

* `drainEcho_exact` (**exact content**): for writer and parsing policies without undefined
  behaviour whose parser sentinel is `z`, and a writer sentinel that is absent or the parser's,
  every related pair `(w, x)` has `x` the byte atom of `w` (`exactRel`).

  Proof: the ghost bridge `Silmaril.Wasm.Game.HandleAccept.MemSound.Ghost.tagTraces_gpre` with the
  chunk buffer of the parsing session as ghost state, a Hoare-logic proof of the ghost obligation
  (the drain empties the at most `16` buffered bytes, `read` then buffers exactly the chunk `blob`
  observes, `finish(n, h)` consumes it; every exit, including the traps and exceptions of every
  call, leaves at most `16` bytes buffered), and assume/guarantee along the chunk buffer.
* `drainEcho_finish_bound`: at every `finish` of a mixed trace whose writes agree with a writer
  store `σ`, at most `16` bytes are buffered, and the handle is a sentinel or denotes in `σ` the
  byte atom of the bytes it consumes.
* `drainEcho_no_stale` (**the stale pair of `blobEcho` is gone**): `(68 69, bytes 69 68)`, related
  by `blobEcho` (`Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix.blobEcho_stale`), is not
  related by `drainEcho z`.
* **Non-vacuity**, for policies whose overrun answer is `callTrap` (the default) or `ignore`:
  `drainEcho_live` (one invocation: `(68 69, bytes 68 69)`), `drainEcho_repeat` (two invocations:
  the second relates `(69 68, bytes 69 68)`), `drainEcho_after_trap` (against `trapEnv q`, whose
  first `blob` traps after `read`: the next invocation drains the two stale bytes and relates
  `(69 68, bytes 69 68)`).

**Policy precondition of the drain.** A drain call `finish(k, z)` with fewer than `k` bytes
buffered is an overrun. Under `onOverrun = callTrap` or `ignore` it relates nothing and keeps the
cursor, so the five calls consume exactly the stale bytes; under `sessionTrap` the first overrun
ends the parsing session, which keeps `drainEcho_exact` true but leaves the relation empty after
it. The module holds no state across invocations (admitted hosts may rewrite globals and memory),
so a protocol that consumes exactly the stale count without probing needs a host-protected
counter, which `blobReply` does not provide.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Exact

open Silmaril.Wasm Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Memory
  Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Pull Silmaril.Wasm.Game.HandleAccept.MemSound.PullMix

variable (P : Profile) {z : BitVec 32}

/-- **`drainEcho z` relates exactly its input bytes to their byte atom.** -/
theorem drainEcho_exact {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) (hsz : ppol.sentinel = z)
    (hs : pol.sentinel = none ∨ pol.sentinel = some ppol.sentinel) :
    memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol ⊆ exactRel :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.exact_of_gsat
    (fun σ => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.de_gsat P
      (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.deOk_all z) pol.sentinel σ)
    (fun _ _ h => h) hw ha hb ho hsz hs

/-- **The guarantee at every `finish`**, read in the chunk buffer before it. -/
theorem drainEcho_finish_bound {sent : Option (BitVec 32)}
    {t : List MixEv} (ht : t ∈ mixTraces P (ReplyEnvs blobReply) 0 (drainEcho z) {} {})
    {σ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    (hWA : WritesAgree (sexpW MemAtom) sent σ t) {u v : List MixEv} {n : Nat} {h : BitVec 32}
    (hd : t = u ++ .p (.finish n h) :: v) :
    (chunkFold [] (parseEvents u)).length ≤ 16 ∧
      (h = z ∨ sent = some h ∨ (n ≤ (chunkFold [] (parseEvents u)).length ∧
        σ h = some (bytesAtom ((chunkFold [] (parseEvents u)).take n)))) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.finish_guarantee
    (fun σ => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.de_gsat P
      (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.deOk_all z) sent σ)
    (fun _ _ h => h) ht hWA hd

/-- **The stale pair of `blobEcho` is not related by `drainEcho z`.** -/
theorem drainEcho_no_stale {pol : Policy (BitVec 32)}
    {ppol : PPolicy (BitVec 32)} (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) (hsz : ppol.sentinel = z)
    (hs : pol.sentinel = none ∨ pol.sentinel = some ppol.sentinel) :
    (([0x68, 0x69] : List UInt8), bytesAtom [0x69, 0x68]) ∉
      memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol := fun h => by
  have := drainEcho_exact P hw ha hb ho hsz hs h
  simp [exactRel, bytesAtom] at this

/-- **One invocation** relates `68 69` to the byte atom `68 69`. -/
theorem drainEcho_live (pol : Policy (BitVec 32))
    (ppol : PPolicy (BitVec 32)) {q : BitVec 32} (hq : pol.sentinel ≠ some q)
    (hpq : ppol.sentinel ≠ q) (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap) :
    (([0x68, 0x69] : List UInt8), bytesAtom [0x68, 0x69]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.de_live P pol ppol hq hpq hov

/-- **Repeated invocations**: the second of two invocations relates `69 68` to its atom. -/
theorem drainEcho_repeat (pol : Policy (BitVec 32))
    (ppol : PPolicy (BitVec 32)) {q₁ q₂ : BitVec 32} (hq₁ : pol.sentinel ≠ some q₁)
    (hpq₁ : ppol.sentinel ≠ q₁) (hq₂ : pol.sentinel ≠ some q₂) (hpq₂ : ppol.sentinel ≠ q₂)
    (hne : q₂ ≠ q₁) (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap) :
    (([0x69, 0x68] : List UInt8), bytesAtom [0x69, 0x68]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.de_repeat P pol ppol hq₁ hpq₁ hq₂ hpq₂
    hne hov

/-- **After an interrupted invocation** (`blob` trapped after `read`), the next invocation drains
the stale bytes and relates `69 68` to its atom. -/
theorem drainEcho_after_trap (pol : Policy (BitVec 32))
    (ppol : PPolicy (BitVec 32)) (hsz : ppol.sentinel = z) {q : BitVec 32}
    (hq : pol.sentinel ≠ some q) (hpq : ppol.sentinel ≠ q)
    (hov : ppol.onOverrun = .ignore ∨ ppol.onOverrun = .callTrap) :
    (([0x69, 0x68] : List UInt8), bytesAtom [0x69, 0x68]) ∈
      memMixedRel P (ReplyEnvs blobReply) 0 (drainEcho z) {} {} pol ppol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Exact.de_after_trap P pol ppol hsz hq hpq hov

end Silmaril.Wasm.Game.HandleAccept.MemSound.Exact
