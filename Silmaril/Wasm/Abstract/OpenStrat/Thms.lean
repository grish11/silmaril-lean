module

public import Silmaril.Wasm.Abstract.OpenStrat.Defs
public import Silmaril.Wasm.Abstract.HostStratXP.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Thms
public import Silmaril.Games.Abstract.StratHost.Thms
public import Silmaril.Games.Abstract.StratOps.Thms
import Silmaril.Proofs.Wasm.Abstract.OpenStrat.Basic

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

**The fixed-host strategies are host restrictions** (`StratHost.hostRestrict`):

* `obsTriple_natXP_eq`, `natStratXP_eq_hostRestrict`: for every host and every question
  predicate `Ok`, the native strategy with exceptions against `host` is the play object of the
  open triple at the questions `Ok`, restricted by `coreHostRel host`. This is an equality of
  triples, before `toDStrat`;
* `natStrat_eq_hostRestrict`: the same, exception-free;
* `coreStratXP_eq_hostRestrict_of` (deterministic profile, the explicit backward hypotheses of
  `coreStratXP_eq_natStratXP_of`), `coreStrat_eq_hostRestrict`: the Core strategies are host
  restrictions of the open native triples.
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

/-- **The Core strategy with exceptions is the host-restricted open native one** (deterministic
profile), given the backward directions of `coreStratXP_eq_natStratXP_of`. -/
theorem coreStratXP_eq_hostRestrict_of {o : GrowOracle} {host : HostSemantics H}
    {tags : List TagInst} (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) (hdiv : BackDivXP o host tags) (hinf : BackInfXP o host tags) :
    coreStratXP (profile o) host (InvOkXP tags) =
      StratObs.toDStrat (hostRestrict (coreHostRel host) (guardT (InvOkXP tags) openTripleXP)) :=
  (coreStratXP_eq_natStratXP_of hT hH hE hdiv hinf).trans (natStratXP_eq_hostRestrict host _)

/-- **The Core strategy is the host-restricted open native one** (deterministic profile, checked
typed invocations). -/
theorem coreStrat_eq_hostRestrict {o : GrowOracle} {host : HostSemantics H} (hT : HostTyped host)
    (hH : NativeHostSlice host) :
    coreStrat (profile o) host InvOk =
      StratObs.toDStrat (hostRestrict (coreHostRel host) (guardT InvOk openTriple)) :=
  (coreStrat_eq_natStrat hT hH).trans (natStrat_eq_hostRestrict host _)

end Silmaril.Wasm.Abstract
