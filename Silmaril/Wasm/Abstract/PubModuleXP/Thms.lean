module

public import Silmaril.Wasm.Abstract.PubModuleXP.Defs
public import Silmaril.Games.Abstract.StratObs.Thms
public import Silmaril.Wasm.Abstract.HostCall.Thms
import Silmaril.Proofs.Wasm.Abstract.PubModuleXP.Basic

/-!
# The public interaction equivalence of an export, with exceptions: theorems

Core side only, against one fixed host, every statement unconditional (no determinism, no typing,
no host square).

**The Core triple with exceptions is recovered from its saturation.** Every call prefix of
`coreTripleXP` is a reached callout (`coreTripleXP_satP_callout`), and its pending calls are
exactly the call prefixes the host leaves pending (`coreTripleXP_pending_eq`). The uncaught
exception end is a run like the value and trap ends, so the argument of
`Silmaril.Wasm.Abstract.PubModule` goes through unchanged.

**The public injection.** `pubStratXP_eq_iff`: the public strategies with exceptions of two
exports are equal iff the exports are `PubEquivXP`, the agreement of the Core observations
`CoreObsLXP` on the admitted invocations (`pubEquivXP_iff_coreObsLXP`). On exports with no
admitted uncaught exception, `PubEquivXP` is `PubEquiv` (`pubEquivXP_of_native`; "native" here
means native stores without exceptions, not the native semantics).

**Reading back.** A completed public round answering an exception `.inr t` with final store
`s₂` is a Core run to `throwing t` at `s₂` (`pubStratXP_mem_throw`); with values, a Core run to
those values (`pubStratXP_mem_ret`); a one-round infinite public play is a productive Core run
(`pubStratXP_mem_inf`).

**Scope.** Exact log: the whole store is visible at every callout, host answer and end. This is
not contextual full abstraction. No theorem relates `pubStratXP` to the native semantics
(`NatObsXP`, `natStratXP`): that comparison waits for the backward square of
`Silmaril.Wasm.Abstract.HostSquareXP`, whose converse directions are not yet proved.

Proofs are in `Silmaril.Proofs.Wasm.Abstract.PubModuleXP.Basic`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}
  {Ok : Store H → Nat × List Val → Prop}

/-! ## The Core triple with exceptions -/

/-- `coreTripleXP` is the triple of `coreStratXP`. -/
theorem coreStratXP_eq_toDStrat :
    coreStratXP P host Ok = StratObs.toDStrat (coreTripleXP P host Ok) := rfl

/-- **Every call prefix of the Core triple with exceptions is a reached callout.** -/
theorem coreTripleXP_satP_callout {s : Store H} {q : Nat × List Val}
    {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (h : x ∈ StratObs.satP (coreTripleXP P host Ok) s q) :
    Ok s q ∧ ∃ c, EvRun P host (invoke s q.1 q.2) x.1 c ∧ AtCallout c x.2 :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.satP_callout h

/-- **The pending Core calls are the call prefixes the host leaves pending.** -/
theorem coreTripleXP_pending_eq (s : Store H) (q : Nat × List Val) :
    (coreTripleXP P host Ok).2.1 s q =
      {x | x ∈ StratObs.satP (coreTripleXP P host Ok) s q ∧ HostPends host x.2} :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.core_pending_eq s q

/-! ## The public injection -/

/-- `PubEquivXP` is the agreement of the Core observations with exceptions on the admitted
invocations. -/
theorem pubEquivXP_iff_coreObsLXP {s s' : Store H} {a a' : Nat} :
    PubEquivXP P host Ok s a s' a' ↔ ∀ vs o,
      (Ok s (a, vs) ∧ CoreObsLXP P host s a vs o) ↔
        (Ok s' (a', vs) ∧ CoreObsLXP P host s' a' vs o) :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.pubEquiv_iff

/-- **The public injection with exceptions**: two exports have the same public strategy iff
they are publicly equivalent. -/
theorem pubStratXP_eq_iff {s s' : Store H} {a a' : Nat} :
    pubStratXP P host Ok s a = pubStratXP P host Ok s' a' ↔ PubEquivXP P host Ok s a s' a' :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.pubStrat_eq_iff

/-- On exports where no admitted Core run ends in an uncaught exception, `PubEquivXP` is
`PubEquiv`. Core only: no native semantics is involved. -/
theorem pubEquivXP_of_native {s s' : Store H} {a a' : Nat}
    (hn : ∀ vs cs t s₂, Ok s (a, vs) → ¬ EvRun P host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩)
    (hn' : ∀ vs cs t s₂, Ok s' (a', vs) →
      ¬ EvRun P host (invoke s' a' vs) cs ⟨s₂, {}, throwing t⟩) :
    PubEquivXP P host Ok s a s' a' ↔ PubEquiv P host Ok s a s' a' :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.pubEquivXP_iff_pubEquiv hn hn'

/-! ## Reading back the public strategy -/

/-- **A completed public round answering an exception** is a Core run to the uncaught exception
`throwing t` with that final store. -/
theorem pubStratXP_mem_throw {s : Store H} {a : Nat} (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (t : Nat) (s₂ : Store H) :
    (.inr (.ask (PUnit.unit, vs)) :: (StratObs.callMoves cs ++
        [.inr (.ans (PUnit.unit, vs) (.inl (((.inr t : List Val ⊕ Nat), s₂), PUnit.unit)))]) :
        List (Move (wasmHostSig H) (pubSig H))) ∈ (pubStratXP P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, throwing t⟩ :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.pubStrat_mem_throw vs cs t s₂

/-- **A completed public round with values** is a Core run to those values with that final
store. -/
theorem pubStratXP_mem_ret {s : Store H} {a : Nat} (vs : List Val)
    (cs : List (Call (wasmHostSig H))) (ws : List Val) (s₂ : Store H) :
    (.inr (.ask (PUnit.unit, vs)) :: (StratObs.callMoves cs ++
        [.inr (.ans (PUnit.unit, vs) (.inl (((.inl ws : List Val ⊕ Nat), s₂), PUnit.unit)))]) :
        List (Move (wasmHostSig H) (pubSig H))) ∈ (pubStratXP P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.pubStrat_mem_ret vs cs ws s₂

/-- **A one-round infinite public play** is a productive Core run. -/
theorem pubStratXP_mem_inf {s : Store H} {a : Nat} (vs : List Val)
    (ω : Nat → Call (wasmHostSig H)) :
    StratObs.streamPlay [] (PUnit.unit, vs) ω ∈ (pubStratXP P host Ok s a).inf ↔
      Ok s (a, vs) ∧ CoreInf P host (invoke s a vs) ω :=
  Silmaril.Proofs.Wasm.Abstract.PubModuleXP.pubStrat_mem_inf vs ω

end Silmaril.Wasm.Abstract
