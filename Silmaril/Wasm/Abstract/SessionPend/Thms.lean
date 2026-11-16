module

public import Silmaril.Wasm.Abstract.HostStrat.Thms
public import Silmaril.Wasm.Abstract.PubModule.Defs
import Silmaril.Proofs.Wasm.Abstract.SessionPend.Basic

/-!
# The pending plays of the Core session

A play of the Core session (`coreSession`) that ends in a host call, after completed session
rounds ending at the store `s`, is in the session iff the call is a call prefix
(`StratObs.satP`) of the store-retaining Core triple `coreTripleS` at `s`
(`StratSession.mem_pending`). These call prefixes are read in pure Core terms:

* `coreTripleS_satP_callout` (every profile, host and question domain): every call prefix
  `(c, m)` is a **reached callout**: a labelled Core run of the invocation from `s` with exactly
  the host calls `c` to a configuration at the host call `m` (`AtCallout`);
* `coreTripleS_satP_iff` (deterministic profile `profile o`, questions with `Ok s q → InvOk s q`,
  a host with typed answers in the native host slice): **conversely**, every reached callout is a
  call prefix. A callout the host leaves pending is a pending call. One the host answers is
  followed by a run that is never stuck at a non-final configuration (`hostSquare_stuck`): it
  ends at values, a trap or a blocked callout, or it diverges (host-free after a log, at a
  host-divergent callout, or productively, `diverges_iff_obs`). Each of these is an observation
  of the triple whose log extends `c` with a call of `m`;
* `coreSession_mem_pending_iff`: hence **a pending play of the Core session** after completed
  rounds is exactly a Core run from the store the rounds leave to a host callout `m`, at exactly
  the log `c`. `coreSession_pending_callout` is the forward direction at every profile.

Without typing the converse fails: a callout the host answers may be followed by a run stuck at
a non-final configuration, which gives the triple no observation.

Proofs in `Silmaril.Proofs.Wasm.Abstract.SessionPend.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop}

/-- **Every call prefix of the store-retaining Core triple is a reached callout.** -/
theorem coreTripleS_satP_callout {s : Store H} {q : Nat × List Val}
    {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : (c, m) ∈ StratObs.satP (coreTripleS P host Ok) s q) :
    Ok s q ∧ ∃ c', EvRun P host (invoke s q.1 q.2) c c' ∧ AtCallout c' m :=
  Silmaril.Proofs.Wasm.Abstract.SessionPend.coreTripleS_satP_callout h

/-- **The call prefixes of the store-retaining Core triple are the reached callouts**
(deterministic profile, typed checked invocations, a host with typed answers in the native host
slice). -/
theorem coreTripleS_satP_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hOk : ∀ s q, Ok s q → InvOk s q) {s : Store H}
    {q : Nat × List Val} {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} :
    (c, m) ∈ StratObs.satP (coreTripleS (SingleThreaded.profile o) host Ok) s q ↔
      Ok s q ∧ ∃ c', EvRun (SingleThreaded.profile o) host (invoke s q.1 q.2) c c' ∧
        AtCallout c' m :=
  Silmaril.Proofs.Wasm.Abstract.SessionPend.coreTripleS_satP_iff hT hH hOk

/-- **A pending play of the Core session is a reached callout**: after completed session rounds
ending at `s`, a play ending in the call `m` after the host calls `c` is a Core run of `q` from
`s`, at exactly the log `c`, to a configuration at the callout `m`. -/
theorem coreSession_pending_callout {s₀ : Store H}
    {rs : List ((Nat × List Val) × List (Call (wasmHostSig H)) × ((List Val ⊕ Nat) ⊕ PUnit))}
    {q : Nat × List Val} {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : StratSession.sroundsMoves rs ++ .inr (.ask q) :: (StratObs.callMoves c ++ [.inl (.ask m)]) ∈
      (coreSession P host Ok s₀).toStrategy) :
    ∃ s, StratThread.Rounds (coreTripleS P host Ok) s₀ rs s ∧ Ok s q ∧
      ∃ c', EvRun P host (invoke s q.1 q.2) c c' ∧ AtCallout c' m :=
  let ⟨s, hrs, hp⟩ := StratSession.mem_pending.1 h
  ⟨s, hrs, coreTripleS_satP_callout hp⟩

/-- **The pending plays of the Core session** (deterministic profile, typed checked
invocations, a host with typed answers in the native host slice): after completed session rounds
ending at `s`, a play ending in the call `m` after the host calls `c` is in the session iff a
Core run of `q` from `s`, at exactly the log `c`, reaches the callout `m`. -/
theorem coreSession_mem_pending_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (hOk : ∀ s q, Ok s q → InvOk s q) {s₀ : Store H}
    {rs : List ((Nat × List Val) × List (Call (wasmHostSig H)) × ((List Val ⊕ Nat) ⊕ PUnit))}
    {q : Nat × List Val} {c : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} :
    StratSession.sroundsMoves rs ++ .inr (.ask q) :: (StratObs.callMoves c ++ [.inl (.ask m)]) ∈
        (coreSession (SingleThreaded.profile o) host Ok s₀).toStrategy ↔
      ∃ s, StratThread.Rounds (coreTripleS (SingleThreaded.profile o) host Ok) s₀ rs s ∧ Ok s q ∧
        ∃ c', EvRun (SingleThreaded.profile o) host (invoke s q.1 q.2) c c' ∧ AtCallout c' m :=
  StratSession.mem_pending.trans <| exists_congr fun _ =>
    and_congr_right fun _ => coreTripleS_satP_iff hT hH hOk

end Silmaril.Wasm.Abstract
