module

public import Silmaril.Wasm.Abstract.LinkCore.Defs
public import Silmaril.Wasm.Abstract.OpenStrat.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXPBack.Thms
public import Silmaril.Wasm.Abstract.PubModule.Thms
public import Silmaril.Wasm.Abstract.PubModuleXP.Thms
public import Silmaril.Games.Abstract.StratHost.Thms
import Silmaril.Proofs.Wasm.Abstract.LinkCore.Basic

/-!
# The closed Core semantics of invocations, host inside: theorems

**Core runs by their host events** (every profile and host):

* `steps_iff_evRun`: a Core run is a labelled run (`EvRun`) at some log;
* `diverges_iff_obs`: a configuration diverges in Core with the host (`Diverges P host`) iff
  after a labelled run it diverges host-free (the `div` observation), or a labelled run reaches a
  callout (`AtCallout`) the host diverges on (`hostDiv`), or it has a productive run (`CoreInf`,
  `prod`: infinitely many answered host calls).

**Linking the Core strategy with its host is the closed Core semantics** (every profile `P`,
host and question domain `Ok`): `comp_hostD_coreStrat`,
`(hostD (coreHostRel host)).comp (coreStrat P host Ok) = toDStrat (closedCore P host Ok)`, from
the equality of triples `linkT_coreTriple`. Clause by clause of `StratHost.linkT`:

* a finished behaviour of the Core triple at any (necessarily allowed) log is a Core run to values
  or to a trap, log erased (`steps_iff_evRun`); a thrown exception is an end of neither side;
* divergence: host-free divergence after a log is a behaviour `(cs, div)` of the Core triple; a
  call prefix of the saturated Core triple at which the host may diverge is a reached callout
  (`coreTriple_satP_callout`), so the Core run stutters there forever; and conversely such a
  callout is a pending call of the Core triple. An allowed productive stream is a productive Core
  run. Together these are `Diverges P host` (`diverges_iff_obs`);
* **blocked callouts agree**: a Core run stuck at a host call the host has no outcome for has no
  end and does not diverge there, so it gives `closedCore` no behaviour; the linked side gives
  none either, since `hostD` is quiescent at such a call (no move, no divergence) and `linkT`
  takes host divergence only at calls `R m .diverge`.

`comp_hostD_coreStratXP`, `linkT_coreTripleXP`: the same with exceptions (`coreStratXP`,
`closedCoreXP`, the uncaught exception `throwing t` as an end).

**The native strategies** (deterministic profile `profile o`):

* `comp_hostD_natStrat` (checked typed invocations `InvOk`, a host with typed answers in the
  native host slice): the open native triple, restricted by the host
  (`hostRestrict (coreHostRel host) (guardT InvOk openTriple)`, the triple of `natStrat`), linked
  with the host, is the closed Core semantics `closedCore (profile o) host InvOk`. Through
  `coreStrat_eq_hostRestrict`;
* `comp_hostD_natStratXP` (`InvOkXP tags`, moreover `HostSliceE tags`): with exceptions, through
  `natStratXP_eq_hostRestrict` and `coreStratXP_eq_natStratXP`.

**Scope.** These link the host-*restricted* native triple. Linking the unrestricted open triple
`guardT InvOk openTriple` (`comp_hostD_openStratXP`) differs only in the host-divergence clause
of `linkT`: there the call prefixes are those of `StratObs.sat` of the open triple, forced also by
behaviours whose later answers the host does not allow. Equating the two needs native
saturation: every call prefix `(c, m)` of a native behaviour, pending call or stream is a native
pending call (`wasmEvPend`, resp. `wasmEvPendXP`). Only its finite-behaviour case is proved, for
the exception-aware closure (`HostClosingXP`, `close_pend`).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratHost
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Core runs by their host events -/

/-- **A Core run is a labelled run** at some log. -/
theorem steps_iff_evRun {c c' : Config H} : Steps P host c c' ↔ ∃ cs, EvRun P host c cs c' :=
  Silmaril.Proofs.Wasm.Abstract.LinkCore.steps_iff_evRun

/-- **Core divergence with the host, by its host events**: host-free divergence after a labelled
run, a labelled run to a callout the host diverges on, or a productive run. -/
theorem diverges_iff_obs {c : Config H} :
    Diverges P host c ↔
      (∃ cs c', EvRun P host c cs c' ∧ Diverges P (fun _ _ _ _ => False) c') ∨
      (∃ cs c', EvRun P host c cs c' ∧ ∃ m, AtCallout c' m ∧ host m.1 m.2.1 m.2.2 .diverged) ∨
      ∃ ω, CoreInf P host c ω :=
  Silmaril.Proofs.Wasm.Abstract.LinkCore.diverges_iff

/-! ## Linking the Core strategy with its host -/

/-- **The link of the Core triple with its host is the closed Core triple.** -/
theorem linkT_coreTriple (Ok : Store H → Nat × List Val → Prop) :
    linkT (coreHostRel host) (coreTriple P host Ok) = closedCore P host Ok :=
  Silmaril.Proofs.Wasm.Abstract.LinkCore.linkT_coreTriple

/-- **Linking the Core strategy with its host is the closed Core semantics**, host interaction
hidden. -/
theorem comp_hostD_coreStrat (Ok : Store H → Nat × List Val → Prop) :
    (hostD (coreHostRel host)).comp (coreStrat P host Ok) =
      StratObs.toDStrat (closedCore P host Ok) :=
  (comp_hostD_toDStrat _ _).trans (congrArg _ (linkT_coreTriple Ok))

/-- **The link of the Core triple with exceptions is the closed Core triple with exceptions.** -/
theorem linkT_coreTripleXP (Ok : Store H → Nat × List Val → Prop) :
    linkT (coreHostRel host) (coreTripleXP P host Ok) = closedCoreXP P host Ok :=
  Silmaril.Proofs.Wasm.Abstract.LinkCore.linkT_coreTripleXP

/-- **Linking the Core strategy with exceptions with its host is the closed Core semantics with
exceptions.** -/
theorem comp_hostD_coreStratXP (Ok : Store H → Nat × List Val → Prop) :
    (hostD (coreHostRel host)).comp (coreStratXP P host Ok) =
      StratObs.toDStrat (closedCoreXP P host Ok) :=
  (comp_hostD_toDStrat _ _).trans (congrArg _ (linkT_coreTripleXP Ok))

/-! ## The native strategies -/

/-- **Linking the host-restricted open native strategy with its host is the closed Core
semantics** (deterministic profile, checked typed invocations, a host with typed answers in the
native host slice). -/
theorem comp_hostD_natStrat {o : GrowOracle} (hT : HostTyped host) (hH : NativeHostSlice host) :
    (hostD (coreHostRel host)).comp
        (StratObs.toDStrat (hostRestrict (coreHostRel host) (guardT InvOk openTriple))) =
      StratObs.toDStrat (closedCore (profile o) host InvOk) :=
  (coreStrat_eq_hostRestrict (o := o) hT hH) ▸ comp_hostD_coreStrat InvOk

/-- **Linking the host-restricted open native strategy with exceptions with its host is the
closed Core semantics with exceptions** (deterministic profile, `InvOkXP tags`, a host with typed
answers in the host slices). -/
theorem comp_hostD_natStratXP {o : GrowOracle} {tags : List TagInst} (hT : HostTyped host)
    (hH : NativeHostSlice host) (hE : HostSliceE tags host) :
    (hostD (coreHostRel host)).comp
        (StratObs.toDStrat (hostRestrict (coreHostRel host) (guardT (InvOkXP tags) openTripleXP))) =
      StratObs.toDStrat (closedCoreXP (profile o) host (InvOkXP tags)) :=
  ((coreStratXP_eq_natStratXP (o := o) hT hH hE).trans
    (natStratXP_eq_hostRestrict host _)) ▸ comp_hostD_coreStratXP (InvOkXP tags)

end Silmaril.Wasm.Abstract
