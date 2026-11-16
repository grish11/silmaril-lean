module

public import Silmaril.Wasm.Abstract.PubModule.Defs
public import Silmaril.Wasm.Abstract.HostStrat.Thms
import Silmaril.Proofs.Wasm.Abstract.PubModule.Basic

/-!
# The public interaction equivalence of an export: theorems

**The Core triple is not saturated, but it is recovered from its saturation.** The pending
calls of the Core triple (`coreTriple`, the triple of `coreStrat`) are the blocked and the
host-divergent callouts. Its call prefixes `StratObs.satP` also contain every call the host
answers on the way to a later observation, so the triple is saturated exactly when the host
leaves every call prefix pending (`coreTriple_saturated_iff`), and it is not saturated as soon
as a returning run makes a call the host answers and does not diverge on
(`coreTriple_not_saturated`). What holds instead needs no hypothesis (no determinism, no
typing): every call prefix is a reached callout (`coreTriple_satP_callout`), and the pending
calls are exactly the call prefixes the host leaves pending (`coreTriple_pending_eq`). So a
Core triple is determined by its saturation, and `StratObs.toDStrat` is injective on Core
triples against a fixed host (`coreStrat_eq_iff`, at any profiles and question domains).

**The public injection.** `pubStrat_eq_iff`: the public strategies of two exports are equal
iff the exports are `PubEquiv`. `PubEquiv` is the agreement of the Core observations
`CoreObsL` on the admitted invocations (`pubEquiv_iff_coreObsL`). Through the commuting square
`hostSquare` the same holds for the native public strategy: at the deterministic profile
`profile o` for checked typed invocations (`natPubStrat_eq_iff`, with `HostTyped` and
`NativeHostSlice`: the hypotheses of `coreStrat_eq_natStrat`), and at every profile for
native-profile stores (`natPubStrat_eq_iff_profile`, moreover `HostNative`).

**Reading back.** A completed public round with values is a Core run to those values with that
final store (`pubStrat_mem_ret`); a one-round infinite public play is a productive Core run
(`pubStrat_mem_inf`).

**Scope.** Native stores: a thrown tag ends no Core run (`coreStrat_not_mem_throw`), so the
public answers `.inr t` are never played. The exception-aware version waits for an
exception-aware `coreStrat`. Not contextual full abstraction: the equivalence is that of the
exact-log observations against one fixed host.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.PubModule.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop}

/-! ## The Core triple and its saturation -/

/-- **Every call prefix of the Core triple is a reached callout.** -/
theorem coreTriple_satP_callout {s : Store H} {q : Nat × List Val}
    {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (h : x ∈ StratObs.satP (coreTriple P host Ok) s q) :
    Ok s q ∧ ∃ c, EvRun P host (invoke s q.1 q.2) x.1 c ∧ AtCallout c x.2 :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.satP_callout h

/-- **The pending Core calls are the call prefixes the host leaves pending.** -/
theorem coreTriple_pending_eq (s : Store H) (q : Nat × List Val) :
    (coreTriple P host Ok).2.1 s q =
      {x | x ∈ StratObs.satP (coreTriple P host Ok) s q ∧ HostPends host x.2} :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.core_pending_eq s q

/-- The Core triple is saturated exactly when the host leaves every call prefix pending. -/
theorem coreTriple_saturated_iff :
    StratObs.Saturated (coreTriple P host Ok) ↔
      ∀ s q x, x ∈ StratObs.satP (coreTriple P host Ok) s q → HostPends host x.2 :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.core_saturated_iff

/-- **The Core triple is not saturated** once a returning run makes a host call that the host
answers and does not diverge on. -/
theorem coreTriple_not_saturated {s : Store H} {q : Nat × List Val}
    {cs cs' : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    {n : (wasmHostSig H).Ar m} {ws : List Val} {s₂ : Store H} (hq : Ok s q)
    (h : EvRun P host (invoke s q.1 q.2) (cs ++ ⟨m, n⟩ :: cs') ⟨s₂, {}, vals ws⟩)
    (hd : ¬ host m.1 m.2.1 m.2.2 .diverged) :
    ¬ StratObs.Saturated (coreTriple P host Ok) :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.core_not_saturated hq h hd

/-- **`toDStrat` is injective on Core triples** against a fixed host. -/
theorem coreStrat_eq_iff {P' : Numerics.Profile} {Ok' : Store H → Nat × List Val → Prop} :
    coreStrat P host Ok = coreStrat P' host Ok' ↔ coreTriple P host Ok = coreTriple P' host Ok' :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.coreStrat_eq_iff

/-! ## The public injection -/

/-- `PubEquiv` is the agreement of the Core observations on the admitted invocations. -/
theorem pubEquiv_iff_coreObsL {s s' : Store H} {a a' : Nat} :
    PubEquiv P host Ok s a s' a' ↔ ∀ vs o,
      (Ok s (a, vs) ∧ CoreObsL P host s a vs o) ↔
        (Ok s' (a', vs) ∧ CoreObsL P host s' a' vs o) :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.pubEquiv_iff

/-- **The public injection**: two exports have the same public strategy iff they are
publicly equivalent. -/
theorem pubStrat_eq_iff {s s' : Store H} {a a' : Nat} :
    pubStrat P host Ok s a = pubStrat P host Ok s' a' ↔ PubEquiv P host Ok s a s' a' :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.pubStrat_eq_iff

/-- The native public strategy is the Core one at the deterministic profile `profile o`, for
checked typed invocations and a host with typed answers in the native host slice. -/
theorem natPubStrat_eq_pubStrat {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) (s : Store H) (a : Nat) :
    natPubStrat host InvOk s a = pubStrat (SingleThreaded.profile o) host InvOk s a :=
  congrArg (fun T => StratObs.toDStrat (pubTriple T s a)) <|
    obsTriple_congr fun _ _ ⟨hs, hS, hok⟩ x => hostSquare hT hH hs hS hok x

/-- **The native public injection** at the deterministic profile. -/
theorem natPubStrat_eq_iff {o : SingleThreaded.GrowOracle} (hT : HostTyped host)
    (hH : Interp.NativeHostSlice host) {s s' : Store H} {a a' : Nat} :
    natPubStrat host InvOk s a = natPubStrat host InvOk s' a' ↔
      PubEquiv (SingleThreaded.profile o) host InvOk s a s' a' := by
  rw [natPubStrat_eq_pubStrat (o := o) hT hH, natPubStrat_eq_pubStrat hT hH]; exact pubStrat_eq_iff

/-- The native public strategy is the Core one at every profile, for checked typed invocations
of stores with native-profile Wasm functions and a host satisfying moreover
`Interp.HostNative`. -/
theorem natPubStrat_eq_pubStrat_profile (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    (hN : Interp.HostNative host) (s : Store H) (a : Nat) :
    natPubStrat host InvOkN s a = pubStrat P host InvOkN s a :=
  congrArg (fun T => StratObs.toDStrat (pubTriple T s a)) <|
    obsTriple_congr fun _ _ ⟨⟨hs, hS, hok⟩, hW⟩ x => hostSquare_profile hT hH hN hs hS hW hok x

/-- **The native public injection** at every profile, for native-profile stores. -/
theorem natPubStrat_eq_iff_profile (hT : HostTyped host) (hH : Interp.NativeHostSlice host)
    (hN : Interp.HostNative host) {s s' : Store H} {a a' : Nat} :
    natPubStrat host InvOkN s a = natPubStrat host InvOkN s' a' ↔
      PubEquiv P host InvOkN s a s' a' := by
  rw [natPubStrat_eq_pubStrat_profile hT hH hN, natPubStrat_eq_pubStrat_profile hT hH hN]
  exact pubStrat_eq_iff

/-! ## Reading back the public strategy -/

/-- **A completed public round with values** is a Core run to those values with that final
store. -/
theorem pubStrat_mem_ret {s : Store H} {a : Nat} (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (ws : List Val) (s₂ : Store H) :
    (.inr (.ask (PUnit.unit, vs)) :: (StratObs.callMoves cs ++
        [.inr (.ans (PUnit.unit, vs) (.inl (((.inl ws : List Val ⊕ Nat), s₂), PUnit.unit)))]) :
        List (Move (wasmHostSig H) (pubSig H))) ∈ (pubStrat P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.pubStrat_mem_ret vs cs ws s₂

/-- **A one-round infinite public play** is a productive Core run. -/
theorem pubStrat_mem_inf {s : Store H} {a : Nat} (vs : List Val)
    (ω : Nat → Call (wasmHostSig H)) :
    StratObs.streamPlay [] (PUnit.unit, vs) ω ∈ (pubStrat P host Ok s a).inf ↔
      Ok s (a, vs) ∧ CoreInf P host (invoke s a vs) ω :=
  Silmaril.Proofs.Wasm.Abstract.PubModule.pubStrat_mem_inf vs ω

end Silmaril.Wasm.Abstract
