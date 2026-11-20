module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Pull.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.PullLive

/-!
# Pull-style chunked input: theorems

* `run_short`: the parsing host relates only inputs of at most `k` values along a trace of
  chunk feeds and finishes of at most `k` values (policies without undefined behaviour).
* `echo_short`: for every profile, every parsing policy without undefined behaviour and every
  set of fixed environments, every input `echoMod` relates against the hosts of `echoReply`
  (`read` returns at most its `cap`) has at most `16` bytes. Proof: a Hoare-logic proof that
  every `finish(used, h)` call has `used ≤ 16` (`used` is what `read(0, 16)` returned), the
  bridge `tagTraces_pre`, and `run_short`.
* `echo_traces`, `echo_live`: against `echoEnv` (`read(0, 16)` writes `68 69` and returns `2`),
  the parsing trace is `[feed [68, 69], finish 2 7]`: the chunk is decoded from the memory
  **after** the answer; `echoMod` relates `68 69` to the tree of `7` in every fixed environment
  where `7` (not the sentinel) denotes a tree.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Pull

open Silmaril.Wasm Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse

/-- **Short finishes relate short inputs.** -/
theorem run_short {V H X : Type} [DecidableEq H] {pol : PPolicy H}
    {ρ : Silmaril.Accept.Handle.Env H X} (hb : pol.onBadHandle ≠ .ub)
    (ho : pol.onOverrun ≠ .ub) {k : Nat} {s : PState V} {t : List (PEv V H)} {s' : PState V}
    {A : Set (List V × X)} (hr : (parser pol ρ).Run s t s' A) (hs : s.phase ≠ .chaos)
    (ht : ∀ e ∈ t, (∃ c, e = .feed c) ∨ ∃ n h, e = .finish n h ∧ n ≤ k) :
    ∀ p ∈ A, p.1.length ≤ k :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull.run_short hb ho hr hs ht

/-- **`echoMod` relates only inputs of at most `16` bytes.** -/
theorem echo_short (P : Profile) {X : Type} {pol : PPolicy (BitVec 32)}
    (hb : pol.onBadHandle ≠ .ub) (ho : pol.onOverrun ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)) :
    inputLang (pullRel P (ReplyEnvs echoReply) 0 echoMod {} pol Rhos) ⊆
      {w | w.length ≤ 16} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull.echo_short P hb ho Rhos

/-- **The parsing trace of `echoMod`** against `echoEnv`. -/
theorem echo_traces (P : Profile) :
    [.feed [0x68, 0x69], .finish 2 7] ∈ pullTraces P (ReplyEnvs echoReply) 0 echoMod {} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull.echo_traces P

/-- **`echoMod` relates the chunk `68 69` it reads to the tree of `7`.** -/
theorem echo_live (P : Profile) {X : Type} (pol : PPolicy (BitVec 32)) (hsent : pol.sentinel ≠ 7)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) X)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) X} (hρ : ρ ∈ Rhos) {x : X} (h7 : ρ 7 = some x) :
    ([0x68, 0x69], x) ∈ pullRel P (ReplyEnvs echoReply) 0 echoMod {} pol Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pull.echo_live P pol hsent hρ h7

end Silmaril.Wasm.Game.HandleAccept.MemSound.Pull
