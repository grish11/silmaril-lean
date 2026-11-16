module

public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Games.Abstract.StratSession.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Wasm.Abstract.OpenStrat.Defs
import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Close
import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Core
import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Pend
import Silmaril.Proofs.Wasm.Abstract.HostClosingS.Triple

/-!
# Session closing: theorems

The session closure `wasmEvFunXPS` keeps the store of every trap, and erasing those stores
(`StratSession.eraseEnd`, `.ret (.inr ()) s ↦ .trap`) gives exactly the canonical closure
`wasmEvFunXP`, with the same logs:

* `wasmEvFunXPS_erase_le`: a session behaviour erases to a canonical one. A trap answer of the
  session relation is, in the canonical relation, a cut call (an answer of more values than the
  callee's result arity, then a trap), and the callee's store-keeping trap, which resolves the trap
  answer by `Shape.Subst.int`, erases to a trap resolving the cut call by `Shape.Subst.intTrap`.
* `le_wasmEvFunXPS_erase`: a canonical behaviour is an erased session one. A call resolved by
  `Shape.Subst.intTrap` (a cut call, or an ordinary one) is reached, and answering it by the
  callee's trap ends the session run; a cut call is never resolved by a return
  (`wasmEvFunXP_ret_len`).
* `wasmEvFunXPS_erase`: the equality of the two; `eraseTrap_wasmEvFunXPS`: the same through
  `StratSession.eraseTrap`, whatever the pending calls and productive streams.
* `wasmEvFunXPS_ne_trap`, `wasmEvFunXPS_noPlainTrap`: the session closure has no plain trap.
* `wasmEvFunXPS_trap_iff`: a store-keeping trap `(cs, ret (inr ()) s₂)` with a log the host allows
  is exactly a Core run of the invocation with the host events `cs` to a trap in **exactly**
  `s₂` (forward every profile, `wasmEvFunXPS_trap_evRun`; backward deterministic). Values and
  exceptions are the canonical ones (`mem_wasmEvFunXPS_ret_iff`, `wasmEvFunXPS_vals_iff`,
  `wasmEvFunXPS_throw_iff`).
* `wasmEvPendXPS_eq`: the session pending calls are the canonical ones.
* `wasmEvFunDXPS_erase`, `eraseTrap_sessionTripleXP`, `sessionTripleXP_noPlainTrap`: the session
  triple erases to `openTripleXP` and keeps every trap's store.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Games.Abstract.StratSession (eraseEnd eraseTrap NoPlainTrap)

variable {H : Type}

/-- **A session behaviour erases to a canonical behaviour**, with the same log. -/
theorem wasmEvFunXPS_erase_le {s : Store H} {p : Nat × List Val}
    {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit.{1})}
    (hy : y ∈ wasmEvFunXPS s p) : (y.1, eraseEnd y.2) ∈ wasmEvFunXP s p :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.close_erase hy

/-- **A canonical behaviour is an erased session behaviour**, with the same log. -/
theorem le_wasmEvFunXPS_erase {s : Store H} {p : Nat × List Val}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (hy : y ∈ wasmEvFunXP s p) :
    ∃ y' ∈ wasmEvFunXPS s p, y'.1 = y.1 ∧ eraseEnd y'.2 = y.2 :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.close_lift hy

/-- **Erasing the stores of traps projects the session closure onto the canonical closure.** -/
theorem wasmEvFunXPS_erase (s : Store H) (p : Nat × List Val) :
    (fun x => (x.1, eraseEnd x.2)) '' wasmEvFunXPS s p = wasmEvFunXP s p := by
  ext y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact wasmEvFunXPS_erase_le hy'
  · intro hy
    obtain ⟨y', hy', h1, h2⟩ := le_wasmEvFunXPS_erase hy
    exact ⟨y', hy', Prod.ext h1 h2⟩

/-- The projection as `StratSession.eraseTrap`, for any pending calls and productive streams. -/
theorem eraseTrap_wasmEvFunXPS
    (P : Silmaril.Games.Abstract.Pending (wasmHostSig H) (Store H) (Nat × List Val))
    (I : Silmaril.Games.Abstract.PInf (wasmHostSig H) (Store H) (Nat × List Val)) :
    (eraseTrap (wasmEvFunXPS, P, I)).1 = wasmEvFunXP :=
  funext fun s => funext fun p => wasmEvFunXPS_erase s p

/-- **The session closure has no plain trap**: every trap keeps its store. -/
theorem wasmEvFunXPS_ne_trap {s : Store H} {p : Nat × List Val}
    {cs : List (Call (wasmHostSig H))} : (cs, .trap) ∉ wasmEvFunXPS s p :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.close_ne_trap

theorem wasmEvFunXPS_noPlainTrap
    (P : Silmaril.Games.Abstract.Pending (wasmHostSig H) (Store H) (Nat × List Val))
    (I : Silmaril.Games.Abstract.PInf (wasmHostSig H) (Store H) (Nat × List Val)) :
    NoPlainTrap (wasmEvFunXPS, P, I) :=
  fun _ _ _ => wasmEvFunXPS_ne_trap


/-! ## Session behaviours and Core runs, at exactly their log and store -/

/-- **A returning session behaviour is exactly a returning canonical behaviour**: values
`inl (inl ws)` and exceptions `inl (inr t)` are the canonical ones. -/
theorem mem_wasmEvFunXPS_ret_iff {s s₂ : Store H} {p : Nat × List Val}
    {cs : List (Call (wasmHostSig H))} {b : List Val ⊕ Nat} :
    (cs, .ret (.inl b) s₂) ∈ wasmEvFunXPS s p ↔ (cs, .ret b s₂) ∈ wasmEvFunXP s p :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.mem_ret_iff

section Core

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)

variable {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}

/-- **A store-keeping trap is a Core run to a trap in exactly its store** (every profile): a
behaviour `(cs, ret (inr ()) s₂)` of `wasmEvFunXPS` with a log the host allows is a Core run of
the invocation with exactly the host events `cs` to a trap in the store `s₂`. -/
theorem wasmEvFunXPS_trap_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {a : Nat} {vs : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inr ()) s₂) ∈ wasmEvFunXPS s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.wasmEvFunXPS_trap_evRun hH hE hts hS hok h hc

/-- **Returning session behaviours are Core runs to their values** (every profile). -/
theorem wasmEvFunXPS_vals_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {a : Nat} {vs ws : List Val} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl (.inl ws)) s₂) ∈ wasmEvFunXPS s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  wasmEvFunXP_vals_evRun hH hE hts hS hok (mem_wasmEvFunXPS_ret_iff.1 h) hc

/-- **Uncaught exceptions of the session closure are Core runs to the thrown exception** (every
profile). -/
theorem wasmEvFunXPS_throw_evRun (hH : NativeHostSlice host) (hE : HostSliceE tags host)
    {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat} (hts : TagsOk tags s)
    (hS : StoreChkE (ehExt tags) s.funcs) (hok : InvokeOk s a vs)
    {cs : List (Call (wasmHostSig H))} (h : (cs, .ret (.inl (.inr t)) s₂) ∈ wasmEvFunXPS s (a, vs))
    (hc : (coreHostRel host).Consistent cs) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩ :=
  wasmEvFunXP_throw_evRun hH hE hts hS hok (mem_wasmEvFunXPS_ret_iff.1 h) hc

end Core

section CoreIff

open Silmaril.Wasm.Interp (NativeHostSlice HostSliceE TagsOk StoreChkE ehExt)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}

/-- **A Core run to a trap in `s₂` is the session trap in exactly `s₂`** (deterministic
profile), with exactly the run's log. -/
theorem evRun_wasmEvFunXPS_trap (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hrun : EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩) :
    (cs, .ret (.inr ()) s₂) ∈ wasmEvFunXPS s (a, vs) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.evRun_wasmEvFunXPS_trap hT hH hE hs hS hts hok hrun

/-- **Store-keeping traps at exactly their log and store, both directions** (deterministic
profile): `(cs, ret (inr ()) s₂)` is a behaviour of `wasmEvFunXPS` with a log the host allows
exactly when the invocation has a Core run with the host events `cs` to a trap in the store
`s₂`. -/
theorem wasmEvFunXPS_trap_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .ret (.inr ()) s₂) ∈ wasmEvFunXPS s (a, vs) ∧ (coreHostRel host).Consistent cs) ↔
      EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ :=
  ⟨fun h => wasmEvFunXPS_trap_evRun hH hE hts hS hok h.1 h.2,
    fun h => ⟨evRun_wasmEvFunXPS_trap hT hH hE hs hS hts hok h, evRun_consistent h⟩⟩

/-- **Returning session behaviours at exactly their log, both directions** (deterministic
profile). -/
theorem wasmEvFunXPS_vals_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs ws : List Val}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .ret (.inl (.inl ws)) s₂) ∈ wasmEvFunXPS s (a, vs) ∧
        (coreHostRel host).Consistent cs) ↔
      EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ := by
  rw [mem_wasmEvFunXPS_ret_iff]
  exact wasmEvFunXP_vals_iff hT hH hE hs hS hts hok

/-- **Uncaught exceptions of the session closure at exactly their log, both directions**
(deterministic profile). -/
theorem wasmEvFunXPS_throw_iff (hT : HostTyped host) (hH : NativeHostSlice host)
    (hE : HostSliceE tags host) {s s₂ : Store H} {a : Nat} {vs : List Val} {t : Nat}
    {cs : List (Call (wasmHostSig H))} (hs : StoreOk s) (hS : StoreChkE (ehExt tags) s.funcs)
    (hts : TagsOk tags s) (hok : InvokeOk s a vs) :
    ((cs, .ret (.inl (.inr t)) s₂) ∈ wasmEvFunXPS s (a, vs) ∧
        (coreHostRel host).Consistent cs) ↔
      EvRun (profile o) host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩ := by
  rw [mem_wasmEvFunXPS_ret_iff]
  exact wasmEvFunXP_throw_iff hT hH hE hs hS hts hok

end CoreIff


/-! ## Pending calls -/

/-- **The session pending calls are the canonical pending calls**: a pending call carries no end,
and the calls before it are answered by values or exceptions, so the store of a trap never enters
it. -/
theorem wasmEvPendXPS_eq : wasmEvPendXPS (H := H) = wasmEvPendXP :=
  funext fun _ => funext fun _ => Set.ext fun _ =>
    ⟨Silmaril.Proofs.Wasm.Abstract.HostClosingS.pendS_toH,
      Silmaril.Proofs.Wasm.Abstract.HostClosingS.pend_toS⟩


/-! ## The session triple -/

/-- **Erasing trap stores sends the session behaviours with divergence onto `wasmEvFunDXP`.** -/
theorem wasmEvFunDXPS_erase (s : Store H) (p : Nat × List Val) :
    (fun x => (x.1, eraseEnd x.2)) '' wasmEvFunDXPS s p = wasmEvFunDXP s p :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.erase_wasmEvFunDXPS s p

/-- **The session triple projects onto the open canonical triple**: `StratSession.eraseTrap`
sends `sessionTripleXP` to `openTripleXP`. -/
theorem eraseTrap_sessionTripleXP : eraseTrap (sessionTripleXP (H := H)) = openTripleXP :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.eraseTrap_sessionTripleXP

/-- **The session triple has no plain trap**: every trap keeps its store. -/
theorem sessionTripleXP_noPlainTrap : NoPlainTrap (sessionTripleXP (H := H)) :=
  Silmaril.Proofs.Wasm.Abstract.HostClosingS.sessionTripleXP_noPlainTrap

end Silmaril.Wasm.Abstract
