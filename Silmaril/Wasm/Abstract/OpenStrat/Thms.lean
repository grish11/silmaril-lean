module

public import Silmaril.Wasm.Abstract.OpenStrat.Defs
public import Silmaril.Wasm.Abstract.HostStratXP.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Thms
public import Silmaril.Games.Abstract.StratHost.Thms
public import Silmaril.Games.Abstract.StratOps.Thms
import Silmaril.Proofs.Wasm.Abstract.OpenStrat.Basic
import Silmaril.Proofs.Wasm.Abstract.OpenStrat.Sat

/-!
# The open, host-independent native strategy of invocations: theorems

**Reading back the open strategy** (`StratObs` readback lemmas, specialised):

* a completed round answering values or an exception is a finished behaviour of `wasmEvFunXP`
  (`openStratXP_mem_ret`), a trap round a trapping one (`openStratXP_mem_trap`);
* a one-round divergent play is a divergent behaviour of `wasmEvFunDXP` (`openStratXP_mem_div`);
* a play ending in a host call is a call prefix of the triple (`openStratXP_mem_pending`); every
  pending call of `wasmEvPendXP` gives one (`openStratXP_pending_mem`);
* a one-round infinite play is a productive stream of `wasmEvInfNXP` (`openStratXP_mem_inf`);
* `readback_openStratXP`: the whole readback is the saturation of `openTripleXP`;
* the same for the exception-free `openStrat` (`openStrat_mem_ret`, …).

**Admissibility** (`StratObs.Admissible`, saturation): every call prefix `(c, m)` forced by the
open triple is a pending call, so `toDStrat` erases nothing and reads the triple back:

* `openTripleXP_admissible`: for `openTripleXP`, the prefixes before a host call of a finished
  behaviour (`wasmEvFunXP`), of a pending call (`wasmEvPendXP`), of a divergent behaviour
  (`wasmEvFunDXP`: descent paths, infinite descent chains, logged local divergence) and of a
  productive stream (`wasmEvInfNXP`) are pending calls of `wasmEvPendXP`;
* `readback_openStratXP_eq`, `toDStrat_eq_openStratXP_iff`: the readback of `openStratXP` is
  `openTripleXP` itself, the only admissible triple with that play object.
* `openTriple_admissible`, `readback_openStrat_eq`, `toDStrat_eq_openStrat_iff`: the same for
  the exception-free `openTriple` (`wasmEvFun`, `wasmEvPend`, `wasmEvFunD`, `wasmEvInfN`).

Proof (`Silmaril.Proofs.Wasm.Abstract.OpenStrat.SatShape`, `SatXP`, `Sat`): at the level of shapes, a
predicate `P x c e` closed under the calls of every open behaviour (an import call is pending after
its resolved prefix; an internal call passes its callee's pending calls to the caller) contains the
call prefixes of `close`, of descent paths and chains, of `closeDLog` and of `closeInfL`, when the
logs of the local divergence and the prefixes of the local streams are closed in the same way. For
`PendLXP` these are descents (`reachLXP_of_descends`) and reaches: every logged call of a logged
local divergence (`LogDivXP`) and of a productive run within a function (`InfLXP`) is reached after
the calls before it. A prefix of a pending call is pending by induction on `PendLXP`, a descent's
prefix being the prefix of a run cutting the reached call (`reachLXP_cut`). Natively the same,
with `PendL`, `LogDiv`, `InfL`, and the reached call answered by an exception (`reachL_throw`).

**The fixed-host strategies are host restrictions** (`StratHost.hostRestrict`):

* `obsTriple_natXP_eq`, `natStratXP_eq_hostRestrict`: for every host and every question
  predicate `Ok`, the native strategy with exceptions against `host` is the play object of the
  open triple at the questions `Ok`, restricted by `coreHostRel host`. This is an equality of
  triples, before `toDStrat`;
* `natStrat_eq_hostRestrict`: the same, exception-free;
* `coreStrat_eq_hostRestrict` (deterministic profile, exception-free): the Core strategy is the
  host restriction of the open native triple. The exception-aware Core form follows once the
  productive backward direction `BackInfXP` is proved.

**Linking with the host** (`comp_hostD_openStratXP`): composing the open strategy with the host
`coreHostRel host` as a strategy without imports (`StratHost.hostD`), host interaction hidden, is
the play object of the closed triple `linkT (coreHostRel host) openTripleXP`
(`StratHost.comp_hostD_toDStrat`).
-/

public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratHost
  Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type}

/-- The moves of a strategy on the invocation interface. -/
local notation "M" H =>
  List (Move (wasmHostSig H) (funSig (Store H) (Nat × List Val) (List Val ⊕ Nat)))

/-! ## Reading back the open strategy with exceptions -/

/-- **A completed round with an answer** is a finished behaviour. -/
theorem openStratXP_mem_ret (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (b : List Val ⊕ Nat) (s₂ : Store H) :
    (.inr (.ask (s, (a, vs))) ::
        (StratObs.callMoves cs ++ [.inr (.ans (s, (a, vs)) (.inl (b, s₂)))]) : M H) ∈
      (openStratXP (H := H)).toStrategy ↔
      (cs, .ret b s₂) ∈ wasmEvFunXP s (a, vs) :=
  (StratObs.mem_ret s (a, vs) cs b s₂).trans (wasmEvFunDXP_of_ne_div nofun)

/-- **A completed trap round** is a trapping behaviour. -/
theorem openStratXP_mem_trap (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask (s, (a, vs))) ::
        (StratObs.callMoves cs ++ [.inr (.ans (s, (a, vs)) (.inr PUnit.unit))]) : M H) ∈
      (openStratXP (H := H)).toStrategy ↔
      (cs, .trap) ∈ wasmEvFunXP s (a, vs) :=
  (StratObs.mem_trap s (a, vs) cs).trans (wasmEvFunDXP_of_ne_div nofun)

/-- **A one-round divergent play** is a divergent behaviour. -/
theorem openStratXP_mem_div (s : Store H) (q : Nat × List Val) (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask (s, q)) :: StratObs.callMoves cs : M H) ∈ (openStratXP (H := H)).div ↔
      (cs, .div) ∈ wasmEvFunDXP s q :=
  StratObs.mem_div (s, q) cs

/-- **A play ending in a host call** is a call prefix of the open triple. -/
theorem openStratXP_mem_pending (s : Store H) (q : Nat × List Val)
    (cs : List (Call (wasmHostSig H))) (m : (wasmHostSig H).Op) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inl (.ask m)]) : M H) ∈
      (openStratXP (H := H)).toStrategy ↔ (cs, m) ∈ StratObs.satP openTripleXP s q :=
  StratObs.mem_pending (s, q) cs m

/-- A pending host call gives a play ending in that call. -/
theorem openStratXP_pending_mem {s : Store H} {q : Nat × List Val}
    {cs : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} (h : (cs, m) ∈ wasmEvPendXP s q) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inl (.ask m)]) : M H) ∈
      (openStratXP (H := H)).toStrategy :=
  StratObs.pending_mem (t := openTripleXP) h

/-- **A one-round infinite play** is a productive stream. -/
theorem openStratXP_mem_inf (s : Store H) (q : Nat × List Val)
    (ω : Nat → Call (wasmHostSig H)) :
    StratObs.streamPlay [] (s, q) ω ∈ (openStratXP (H := H)).inf ↔ ω ∈ wasmEvInfNXP s q :=
  StratObs.mem_inf (s, q) ω

/-- **The readback of the open strategy** is the saturated open triple. -/
theorem readback_openStratXP :
    StratOps.readback (openStratXP (H := H)) = StratObs.sat openTripleXP :=
  StratOps.readback_toDStrat _

/-! ## Reading back the exception-free open strategy -/

/-- A completed round with an answer is a finished behaviour. -/
theorem openStrat_mem_ret (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (b : List Val ⊕ Nat) (s₂ : Store H) :
    (.inr (.ask (s, (a, vs))) ::
        (StratObs.callMoves cs ++ [.inr (.ans (s, (a, vs)) (.inl (b, s₂)))]) : M H) ∈
      (openStrat (H := H)).toStrategy ↔
      (cs, .ret b s₂) ∈ wasmEvFun s (a, vs) :=
  (StratObs.mem_ret s (a, vs) cs b s₂).trans (wasmEvFunD_of_ne_div nofun)

/-- A completed trap round is a trapping behaviour. -/
theorem openStrat_mem_trap (s : Store H) (a : Nat) (vs : List Val)
    (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask (s, (a, vs))) ::
        (StratObs.callMoves cs ++ [.inr (.ans (s, (a, vs)) (.inr PUnit.unit))]) : M H) ∈
      (openStrat (H := H)).toStrategy ↔
      (cs, .trap) ∈ wasmEvFun s (a, vs) :=
  (StratObs.mem_trap s (a, vs) cs).trans (wasmEvFunD_of_ne_div nofun)

/-- A one-round divergent play is a divergent behaviour. -/
theorem openStrat_mem_div (s : Store H) (q : Nat × List Val) (cs : List (Call (wasmHostSig H))) :
    (.inr (.ask (s, q)) :: StratObs.callMoves cs : M H) ∈ (openStrat (H := H)).div ↔
      (cs, .div) ∈ wasmEvFunD s q :=
  StratObs.mem_div (s, q) cs

/-- A pending host call gives a play ending in that call. -/
theorem openStrat_pending_mem {s : Store H} {q : Nat × List Val}
    {cs : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op} (h : (cs, m) ∈ wasmEvPend s q) :
    (.inr (.ask (s, q)) :: (StratObs.callMoves cs ++ [.inl (.ask m)]) : M H) ∈
      (openStrat (H := H)).toStrategy :=
  StratObs.pending_mem (t := openTriple) h

/-- A one-round infinite play is a productive stream. -/
theorem openStrat_mem_inf (s : Store H) (q : Nat × List Val) (ω : Nat → Call (wasmHostSig H)) :
    StratObs.streamPlay [] (s, q) ω ∈ (openStrat (H := H)).inf ↔ ω ∈ wasmEvInfN s q :=
  StratObs.mem_inf (s, q) ω

/-! ## Admissibility -/

/-- **The open triple with exceptions is admissible**: every call prefix forced by a finished or
divergent behaviour, by a pending call or by a productive stream is a pending call. -/
theorem openTripleXP_admissible : StratObs.Admissible (openTripleXP (H := H)) :=
  StratObs.saturated_iff.2 <| funext fun s => funext fun p =>
    Set.Subset.antisymm (Silmaril.Proofs.Wasm.Abstract.OpenStrat.satP_openTripleXP_le s p)
      fun _ h => .inl h

/-- **The readback of the open strategy with exceptions is the open triple.** -/
theorem readback_openStratXP_eq :
    StratOps.readback (openStratXP (H := H)) = openTripleXP :=
  readback_openStratXP.trans openTripleXP_admissible

/-- **`toDStrat` is injective at `openTripleXP`**: an admissible triple with the play object of
the open strategy with exceptions is the open triple. -/
theorem toDStrat_eq_openStratXP_iff
    {t : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat)}
    (ht : StratObs.Admissible t) : StratObs.toDStrat t = openStratXP ↔ t = openTripleXP :=
  ⟨fun h => StratObs.toDStrat_injective ht openTripleXP_admissible h, fun h => h ▸ rfl⟩

/-- **The exception-free open triple is admissible.** -/
theorem openTriple_admissible : StratObs.Admissible (openTriple (H := H)) :=
  StratObs.saturated_iff.2 <| funext fun s => funext fun p =>
    Set.Subset.antisymm (Silmaril.Proofs.Wasm.Abstract.OpenStrat.satP_openTriple_le s p)
      fun _ h => .inl h

/-- **The readback of the exception-free open strategy is the open triple.** -/
theorem readback_openStrat_eq : StratOps.readback (openStrat (H := H)) = openTriple :=
  (StratOps.readback_toDStrat _).trans openTriple_admissible

/-- **`toDStrat` is injective at `openTriple`.** -/
theorem toDStrat_eq_openStrat_iff
    {t : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat)}
    (ht : StratObs.Admissible t) : StratObs.toDStrat t = openStrat ↔ t = openTriple :=
  ⟨fun h => StratObs.toDStrat_injective ht openTriple_admissible h, fun h => h ▸ rfl⟩

/-! ## The fixed-host strategies are host restrictions -/

/-- **The native triple with exceptions against `host` is the host restriction of the open
triple** at the questions `Ok`. -/
theorem obsTriple_natXP_eq (host : HostSemantics H) (Ok : Store H → Nat × List Val → Prop) :
    obsTriple Ok (fun s q => NatObsXP host s q.1 q.2) =
      hostRestrict (coreHostRel host) (guardT Ok openTripleXP) :=
  Silmaril.Proofs.Wasm.Abstract.OpenStrat.obsTriple_natXP host Ok

/-- **The native strategy with exceptions against `host` is the host-restricted open one.** -/
theorem natStratXP_eq_hostRestrict (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    natStratXP host Ok =
      StratObs.toDStrat (hostRestrict (coreHostRel host) (guardT Ok openTripleXP)) :=
  congrArg StratObs.toDStrat (obsTriple_natXP_eq host Ok)

/-- **The native strategy against `host` is the host-restricted open one** (exception-free). -/
theorem natStrat_eq_hostRestrict (host : HostSemantics H)
    (Ok : Store H → Nat × List Val → Prop) :
    natStrat host Ok = StratObs.toDStrat (hostRestrict (coreHostRel host) (guardT Ok openTriple)) :=
  congrArg StratObs.toDStrat (Silmaril.Proofs.Wasm.Abstract.OpenStrat.obsTriple_nat host Ok)

/-- **The Core strategy is the host-restricted open native one** (deterministic profile, checked
typed invocations). -/
theorem coreStrat_eq_hostRestrict {o : GrowOracle} {host : HostSemantics H} (hT : HostTyped host)
    (hH : NativeHostSlice host) :
    coreStrat (profile o) host InvOk =
      StratObs.toDStrat (hostRestrict (coreHostRel host) (guardT InvOk openTriple)) :=
  (coreStrat_eq_natStrat hT hH).trans (natStrat_eq_hostRestrict host _)

/-! ## Linking with the host -/

/-- **Linking the open native strategy with a host**: interaction with the host as a strategy,
host calls hidden, is the closed linked triple. -/
theorem comp_hostD_openStratXP (host : HostSemantics H) :
    (hostD (coreHostRel host)).comp (openStratXP (H := H)) =
      StratObs.toDStrat (linkT (coreHostRel host) openTripleXP) :=
  comp_hostD_toDStrat _ _

end Silmaril.Wasm.Abstract
