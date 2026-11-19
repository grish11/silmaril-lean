module

public import Silmaril.Wasm.Abstract.HostSquareXP.Defs
public import Silmaril.Wasm.Abstract.HostSquare.Thms
public import Silmaril.Wasm.Abstract.HostClosingInfXP.Thms
import Silmaril.Proofs.Wasm.Abstract.HostSquareXP.Basic

/-!
# The exact-log commuting square for the canonical closure: theorems

Proofs in `Silmaril.Proofs.Wasm.Abstract.HostSquareXP`. Deterministic profile `profile o`; a host
with typed answers (`HostTyped host`) in the typed host slice (`Interp.HostSliceT host`, possibly
throwing) whose answers keep the exception checker's store check and the tag invariants
(`Interp.HostSliceE tags host`); a typed store (`StoreOk s`) with the exception checker's store
check (`Interp.StoreChkE (Interp.ehExt tags) s.funcs`) and the tag invariants
(`Interp.TagsOk tags s`); a typed invocation (`InvokeOk s a vs`). Every log is exact.

* `hostSquareXP_done`: finished ends. Values, an uncaught exception and a trap from
  `wasmEvFunXP_vals_iff`, `wasmEvFunXP_throw_iff` and `wasmEvFunXP_trap_iff`: the exception is the
  Core run to `throwing t` at the same store, in the empty frame; the trap carries no store. `div`
  is on neither side (`wasmEvFunXP_ne_div`);
* `hostSquareXP_blocked`, `hostSquareXP_hostDiv`: pending host calls with no host outcome, and
  those the host diverges on (`wasmEvPendXP_evRun_iff`);
* `hostSquareXP_div_of`, `hostSquareXP_prod_of`, `hostSquareXP_of`: divergence after a log and
  productive runs, and so the whole square, from the forward theorems of
  `Silmaril.Wasm.Abstract.HostClosingInfXP` (`wasmEvFunDXP_div_evRun`,
  `hostObsInf_wasmEvInfNXP_coreInf`) and the two converse directions (a Core run then host-free
  divergence is `(cs, div) ∈ wasmEvFunDXP`; a productive Core run is in `wasmEvInfNXP`) as
  explicit hypotheses.

The converse directions are proved in `HostClosingInfXPBack` (`evRun_wasmEvFunDXP_div`,
`coreInf_wasmEvInfNXP`), with the unconditional `hostSquareXP_div`, `hostSquareXP_prod` and the
whole square `hostSquareXP` there.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (HostSliceT HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}
  {s : Store H} {a : Nat} {vs : List Val}

/-- **Finished ends at exactly their log** (deterministic profile): values, an uncaught exception
and a trap; `div` is on neither side. -/
theorem hostSquareXP_done (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) (cs : List (Call (wasmHostSig H)))
    (e : End (Store H) (List Val ⊕ Nat)) :
    NatObsXP host s a vs (.done cs e) ↔ CoreObsLXP (profile o) host s a vs (.done cs e) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquareXP.square_done hT hH hE hs hS hts hok cs e

/-- **Pending calls with no host outcome, at exactly their log** (deterministic profile). -/
theorem hostSquareXP_blocked (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) (cs : List (Call (wasmHostSig H)))
    (m : (wasmHostSig H).Op) :
    NatObsXP host s a vs (.blocked cs m) ↔ CoreObsLXP (profile o) host s a vs (.blocked cs m) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquareXP.square_blocked hT hH hE hs hS hts hok cs m

/-- **Pending calls the host diverges on, at exactly their log** (deterministic profile). -/
theorem hostSquareXP_hostDiv (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) (cs : List (Call (wasmHostSig H)))
    (m : (wasmHostSig H).Op) :
    NatObsXP host s a vs (.hostDiv cs m) ↔ CoreObsLXP (profile o) host s a vs (.hostDiv cs m) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquareXP.square_hostDiv hT hH hE hs hS hts hok cs m

/-- **Divergence after a log**, given the converse direction `hdiv`. -/
theorem hostSquareXP_div_of (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hdiv : ∀ (cs : List (Call (wasmHostSig H))) (c' : Config H),
      EvRun (profile o) host (invoke s a vs) cs c' →
      Diverges (profile o) (fun _ _ _ _ => False) c' → (cs, .div) ∈ wasmEvFunDXP s (a, vs))
    (cs : List (Call (wasmHostSig H))) :
    NatObsXP host s a vs (.div cs) ↔ CoreObsLXP (profile o) host s a vs (.div cs) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquareXP.square_div_of hH hE hS hts hok hdiv cs

/-- **Productive runs**, given the converse direction `hinf`. -/
theorem hostSquareXP_prod_of (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hinf : ∀ ω : Nat → Call (wasmHostSig H), CoreInf (profile o) host (invoke s a vs) ω →
      ω ∈ wasmEvInfNXP s (a, vs))
    (ω : Nat → Call (wasmHostSig H)) :
    NatObsXP host s a vs (.prod ω) ↔ CoreObsLXP (profile o) host s a vs (.prod ω) :=
  Silmaril.Proofs.Wasm.Abstract.HostSquareXP.square_prod_of hH hE hS hts hok hinf ω

/-- **The square, given the two converse directions** `hdiv` and `hinf` (deterministic
profile). -/
theorem hostSquareXP_of (hT : HostTyped host) (hH : HostSliceT host)
    (hE : HostSliceE tags host) (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hdiv : ∀ (cs : List (Call (wasmHostSig H))) (c' : Config H),
      EvRun (profile o) host (invoke s a vs) cs c' →
      Diverges (profile o) (fun _ _ _ _ => False) c' → (cs, .div) ∈ wasmEvFunDXP s (a, vs))
    (hinf : ∀ ω : Nat → Call (wasmHostSig H), CoreInf (profile o) host (invoke s a vs) ω →
      ω ∈ wasmEvInfNXP s (a, vs))
    (x : FullObs H) : NatObsXP host s a vs x ↔ CoreObsLXP (profile o) host s a vs x :=
  Silmaril.Proofs.Wasm.Abstract.HostSquareXP.square_of hT hH hE hs hS hts hok hdiv hinf x

end Silmaril.Wasm.Abstract
