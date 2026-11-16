module

public import Silmaril.Wasm.Abstract.BodyDet.Defs
public import Silmaril.Wasm.Abstract.PubModuleXP.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Games.Abstract.StratSession.Thms
public import Silmaril.Wasm.Abstract.HostStrat.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
import Silmaril.Wasm.Abstract.BodyDet.Thms
import Silmaril.Proofs.Wasm.Abstract.CoreDet.Basic

/-!
# The Core host triple is deterministic at the deterministic profile

At the deterministic profile `SingleThreaded.profile o`, against a fixed host `host` whose
answers are typed (`HostTyped`), on questions that are typed invocations of a typed store
(`Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2`, e.g. `InvOk`, `InvOkN`, `InvOkXP tags`):

* `coreTriple_det`, `coreTripleXP_det`: **the saturation of the Core triple is deterministic
  given answers** (`TripleDet`), without and with uncaught exceptions as finished ends.
  - `fin`: two finished behaviours (values, exception, trap, or host-free divergence `.div`)
    make the same host call after every common log, and with the same log they have the same
    end. In particular no log both ends in values or a trap and diverges host-free.
  - `pend`: after each log there is at most one call prefix (`StratObs.satP`): one reached
    callout.
  - `excl`: no log is both the log of a finished behaviour and followed by a call. This covers
    a host that both answers and diverges on one call: the call is pending after its log `c`,
    and the answered continuations have the longer logs `c ++ [x]`.
  - `inf`: the prefixes of a productive run are call prefixes (by the definition of `satP`).
* `coreStrat_pdet`, `pubStrat_pdet`, `coreStratXP_pdet`, `pubStratXP_pdet` (and
  `pubStrat_pdet_invOk`, `pubStratXP_pdet_invOkXP` on the usual domains): hence **the Core
  strategies and the public strategies of exports have at most one Proponent move after each
  play** (`PDet`).

**Why the saturation.** `toDStrat_pdet` asks for a saturated triple, and the Core triple is not
saturated as soon as the host answers a call (`coreTriple_not_saturated`). The play object only
sees the saturation (`StratObs.toDStrat_sat`), which is saturated, so `toDStrat_pdet_of_sat`
asks for `TripleDet (sat t)`: the conditions stated for the call prefixes `satP t`.

**Proponent determinism only.** Proponent is the Wasm side: its moves are the host calls it makes
(host function, store and arguments) and the final answer of a round. Opponent's moves, the host
answers, are not constrained: the host is a relation, which may answer one call in several ways,
diverge on it, both, or neither. Proponent's next move is a function of the play so far, host
answers included.

**Why it holds.** Core reduction at `profile o` is deterministic only up to trap bubbling
(`Step.deterministic_profile`: two successors join within one step). Every configuration a
behaviour is read at (values, `throwing t` or `[trap]` in the empty frame, a callout) has no
host-free step, so a labelled run to it passes through every host-free step
(`evRunN_through`). Hence there is one such configuration per log; bubbling makes no
difference, since even the trap configuration is unique. At a host event both runs are at the
same callout, where the answer in the log fixes the next configuration.

**Hypotheses.** Typing is used only for divergent ends. It excludes that a configuration both
diverges host-free and reaches an end, or a callout, with the same log. A divergent trace is
redirected through every host-free step (`diverges_through_steps`), which needs a typed
configuration (`Sim.ContextTyped`). The reached configuration is typed because it comes from a
typed invocation through typed host answers (`ContextTyped.steps_typed`, `HostTyped`). No
counterexample without typing is known: the hypothesis is the one the available Core lemma
needs. Nondeterministic profiles are not covered, since there one history may have several
results.

**Sessions.** The store-retaining Core triple `coreTripleS` (traps keep their store) is
deterministic given answers too (`coreTripleS_det`): the trap configuration after a log is
unique. Hence it is store-deterministic (`coreTripleS_storeDet`) and the infinite plays of the
Core session are coherent (`coreSession_mem_inf_iff`). With exceptions, the same for the
store-retaining triple `coreTripleSXP` and the session `coreSessionXP` (`coreTripleSXP_det`,
`coreTripleSXP_storeDet`, `coreSessionXP_mem_inf_iff`).

Proofs are in `Silmaril.Proofs.Wasm.Abstract.CoreDet.Basic`.
-/

public section

namespace Silmaril.Wasm.Abstract.CoreDet

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
  Silmaril.Wasm.Abstract.BodyDet

universe u

/-- **The play object of a triple with a deterministic saturation has at most one Proponent move
after each play.** -/
theorem toDStrat_pdet_of_sat {E : Sig.{u}} {S A B : Type u} {t : ObsTriple E S A B}
    (hd : TripleDet (StratObs.sat t)) : PDet (StratObs.toDStrat t).toStrategy :=
  StratObs.toDStrat_sat (t := t) ▸ toDStrat_pdet StratObs.saturated_sat hd

variable {H : Type} {host : HostSemantics H} {o : SingleThreaded.GrowOracle}
  {Ok : Store H → Nat × List Val → Prop}

/-- **The saturated Core triple is deterministic given answers** at the deterministic profile,
for a host with typed answers, on typed invocations of typed stores. This is determinism of the
Wasm side (Proponent) given the host answers in the log; the host answers (Opponent) are
unconstrained. -/
theorem coreTriple_det (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    TripleDet (StratObs.sat (coreTriple (SingleThreaded.profile o) host Ok)) :=
  Silmaril.Proofs.Wasm.Abstract.CoreDet.coreTriple_det hT hOk

/-- **The Core strategy is Proponent-deterministic** at the deterministic profile. -/
theorem coreStrat_pdet (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    PDet (coreStrat (SingleThreaded.profile o) host Ok).toStrategy :=
  toDStrat_pdet_of_sat (coreTriple_det hT hOk)

/-- **The public strategy of an export is Proponent-deterministic** at the deterministic
profile: after each play, at most one host call or final answer by Wasm. The host answers are
Opponent moves, not constrained. -/
theorem pubStrat_pdet (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) (s : Store H) (a : Nat) :
    PDet (pubStrat (SingleThreaded.profile o) host Ok s a).toStrategy :=
  toDStrat_pdet_of_sat (Silmaril.Proofs.Wasm.Abstract.CoreDet.pubTriple_det
    (coreTriple_det hT hOk) s a)

/-- `pubStrat_pdet` on checked typed invocations. -/
theorem pubStrat_pdet_invOk (hT : HostTyped host) (s : Store H) (a : Nat) :
    PDet (pubStrat (SingleThreaded.profile o) host InvOk s a).toStrategy :=
  pubStrat_pdet hT (fun _ _ h => ⟨h.1, h.2.2⟩) s a

/-! ## Sessions -/

/-- **The store-retaining Core triple is deterministic given answers** at the deterministic
profile: two finished behaviours (values, a trap with its store, or host-free divergence) make
the same host call after every common log, and with the same log they have the same end, the
trap store included. The extra fact over `coreTriple_det` is that the trap configuration
`⟨s₂, {}, [.trap]⟩` reached after a log is unique. -/
theorem coreTripleS_det (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    AFun.Det (coreTripleS (SingleThreaded.profile o) host Ok).1 :=
  Silmaril.Proofs.Wasm.Abstract.CoreDet.coreTripleS_det hT hOk

/-- **The store-retaining Core triple is store-deterministic**, so the Core session identifies
exactly the observationally equivalent stores (`StratSession.threadS_eq_iff`). -/
theorem coreTripleS_storeDet (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    StratThread.StoreDet (coreTripleS (SingleThreaded.profile o) host Ok) :=
  StratThread.storeDet_of_det (coreTripleS_det hT hOk)

/-- **The infinite plays of the Core session are coherent** at the deterministic profile: a
productive Core run after completed session rounds, or the play of a coherent infinite sequence
of session rounds (values or traps, each from the store the previous one left). -/
theorem coreSession_mem_inf_iff (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) {s₀ : Store H}
    {I : Set (List (Move (wasmHostSig H) (sig1 (Nat × List Val) (List Val ⊕ Nat))))} :
    I ∈ (coreSession (SingleThreaded.profile o) host Ok s₀).inf ↔
      (∃ rs s q ω, StratThread.Rounds (coreTripleS (SingleThreaded.profile o) host Ok) s₀ rs s ∧
        (Ok s q ∧ CoreInf (SingleThreaded.profile o) host (invoke s q.1 q.2) ω) ∧
        I = StratThread.streamPlay (StratSession.sroundsMoves rs) q ω) ∨
      ∃ a r s, StratThread.InfRounds (coreTripleS (SingleThreaded.profile o) host Ok) s₀ a r s ∧
        I = StratSession.sroundsPlay a r :=
  StratSession.mem_inf_iff_of_det (coreTripleS_det hT hOk)

/-! ## With exceptions -/

/-- **The saturated Core triple with exceptions is deterministic given answers** at the
deterministic profile. -/
theorem coreTripleXP_det (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    TripleDet (StratObs.sat (coreTripleXP (SingleThreaded.profile o) host Ok)) :=
  Silmaril.Proofs.Wasm.Abstract.CoreDet.coreTripleXP_det hT hOk

/-- **The Core strategy with exceptions is Proponent-deterministic.** -/
theorem coreStratXP_pdet (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    PDet (coreStratXP (SingleThreaded.profile o) host Ok).toStrategy :=
  toDStrat_pdet_of_sat (coreTripleXP_det hT hOk)

/-- **The public strategy of an export with exceptions is Proponent-deterministic.** -/
theorem pubStratXP_pdet (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) (s : Store H) (a : Nat) :
    PDet (pubStratXP (SingleThreaded.profile o) host Ok s a).toStrategy :=
  toDStrat_pdet_of_sat (Silmaril.Proofs.Wasm.Abstract.CoreDet.pubTriple_det
    (coreTripleXP_det hT hOk) s a)

/-- `pubStratXP_pdet` on the exception-aware domain `InvOkXP tags`. -/
theorem pubStratXP_pdet_invOkXP (hT : HostTyped host) (tags : List TagInst) (s : Store H)
    (a : Nat) : PDet (pubStratXP (SingleThreaded.profile o) host (InvOkXP tags) s a).toStrategy :=
  pubStratXP_pdet hT (fun _ _ h => ⟨h.1, h.2.2.2⟩) s a

/-! ## Sessions with exceptions -/

/-- **The store-retaining Core triple with exceptions is deterministic given answers** at the
deterministic profile: values, an uncaught exception or a trap, each with its store, or host-free
divergence; with the same log, the same end. -/
theorem coreTripleSXP_det (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    AFun.Det (coreTripleSXP (SingleThreaded.profile o) host Ok).1 :=
  Silmaril.Proofs.Wasm.Abstract.CoreDet.coreTripleSXP_det hT hOk

/-- **The store-retaining Core triple with exceptions is store-deterministic.** -/
theorem coreTripleSXP_storeDet (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) :
    StratThread.StoreDet (coreTripleSXP (SingleThreaded.profile o) host Ok) :=
  StratThread.storeDet_of_det (coreTripleSXP_det hT hOk)

/-- **The infinite plays of the Core session with exceptions are coherent** at the deterministic
profile: a productive Core run after completed session rounds, or the play of a coherent infinite
sequence of session rounds. -/
theorem coreSessionXP_mem_inf_iff (hT : HostTyped host)
    (hOk : ∀ s q, Ok s q → StoreOk s ∧ InvokeOk s q.1 q.2) {s₀ : Store H}
    {I : Set (List (Move (wasmHostSig H) (sig1 (Nat × List Val) (List Val ⊕ Nat))))} :
    I ∈ (coreSessionXP (SingleThreaded.profile o) host Ok s₀).inf ↔
      (∃ rs s q ω,
        StratThread.Rounds (coreTripleSXP (SingleThreaded.profile o) host Ok) s₀ rs s ∧
        (Ok s q ∧ CoreInf (SingleThreaded.profile o) host (invoke s q.1 q.2) ω) ∧
        I = StratThread.streamPlay (StratSession.sroundsMoves rs) q ω) ∨
      ∃ a r s,
        StratThread.InfRounds (coreTripleSXP (SingleThreaded.profile o) host Ok) s₀ a r s ∧
        I = StratSession.sroundsPlay a r :=
  StratSession.mem_inf_iff_of_det (coreTripleSXP_det hT hOk)

end Silmaril.Wasm.Abstract.CoreDet
