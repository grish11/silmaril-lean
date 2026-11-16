module

public import Silmaril.Games.Abstract.SessionExt.Defs
public import Silmaril.Games.Abstract.SessionRoute.Thms
public import Silmaril.Games.Abstract.SessionPairMap.Defs
import Silmaril.Proofs.Games.Abstract.SessionExt.Basic

/-!
# Extending an environment by a session node, on session interfaces: theorems

**Extending a session environment by a session node is a linked session** (`extS_threadS`): for
an environment session `threadS u s'` (`u : ObsTriple X S' A (B ⊕ PUnit)`), a node session
`threadS t s` running over it (`t : ObsTriple (sig1 A B) S A₂ (B ⊕ PUnit)`), and a routing
`r : A → A ⊕ A₂` of outer questions to copycat (`.inl`) or to the node (`.inr`),

  `extS r (threadS u s') (threadS t s) = threadS (linkS u (routeS r idS t)) (s', ((), s))`,

when `u` and `t` have no plain traps and deterministic returns (`SessionCat.RetDet`). The outer
session is the environment's session linked with the client `routeS r idS t`: the identity
session `SessionCat.idS` (copycat on the environment's functions) beside the node, questions
routed by `r`, answers of both sides merged.

The steps:

* `relabelPair_eq_mapAns`: `StratSession.relabelPair` is the answer relabelling
  `DStrategy.mapAns pairAnswer`, hence composition with `ansH pairAnswer` (`DStrategy.comp_ansH`).
* `ofHandler_routeH`: the routing handler is `ansH pairAnswer` followed by the one-call handler
  `callH r (fun _ => foldS)` on the paired session interface; both are sessions
  (`SessionRoute.threadS_callS`), linked by `SessionRoute.threadS_comp_callH` (`mapS_callS`).
* `pair_comp_routeH`: two sessions side by side below `routeH r` are the session of
  `routeS r t₁ t₂`: relabel the pairing into the paired session (`StratSession.threadS_pairS`),
  then route it (`SessionRoute.threadS_comp_callH`). Pairing and routing keep the absence of
  plain traps and deterministic returns (`retDet_pairS`, `noPlainTrap_routeS`,
  `retDet_routeS`).
* `extS_threadS`: copycat is the session of `idS` (`SessionCat.threadS_idS`); the environment's
  session serves the routed session (`SessionLink.comp_threadS`, with `SessionCat.retDet_linkS`).

Proofs are in `Silmaril.Proofs.Games.Abstract.SessionExt`.
-/

public section

namespace Silmaril.Games.Abstract.SessionExt

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionLink Silmaril.Games.Abstract.SessionCat
  Silmaril.Games.Abstract.SessionRoute

universe u

section Pair

variable {E : Sig.{u}} {A₁ A₂ B₁ B₂ : Type u}

/-- **`relabelPair` relabels answers along `pairAnswer`.** -/
theorem relabelPair_eq_mapAns (σ : DStrategy E (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂)) :
    relabelPair σ = σ.mapAns pairAnswer :=
  Silmaril.Proofs.Games.Abstract.SessionExt.relabelPair_eq_mapAns σ

/-- **Pairing keeps deterministic returns.** -/
theorem retDet_pairS {S₁ S₂ : Type u} {t₁ : ObsTriple E S₁ A₁ (B₁ ⊕ PUnit.{u + 1})}
    {t₂ : ObsTriple E S₂ A₂ (B₂ ⊕ PUnit.{u + 1})} (h₁ : RetDet t₁) (h₂ : RetDet t₂) :
    RetDet (pairS t₁ t₂) :=
  Silmaril.Proofs.Games.Abstract.SessionExt.retDet_pairS h₁ h₂

end Pair

/-- **Mapping a one-call triple is a one-call triple.** -/
theorem mapS_callS {E : Sig.{u}} {A A' B B' : Type u} (g : A → E.Op)
    (f : (a : A) → E.Ar (g a) → B ⊕ PUnit.{u + 1}) (g' : A' → A)
    (f' : A' → B ⊕ PUnit.{u + 1} → B' ⊕ PUnit.{u + 1}) :
    mapS g' f' (callS g f) = callS (fun a => g (g' a)) (fun a n => f' a (f (g' a) n)) :=
  Silmaril.Proofs.Games.Abstract.SessionExt.mapS_callS g f g' f'

variable {A A₁ A₂ B : Type u}

/-- **The routing handler factors** through the paired session interface. -/
theorem ofHandler_routeH (r : A → A₁ ⊕ A₂) :
    DStrategy.ofHandler (routeH (B := B) r) =
      (DStrategy.ofHandler (ansH (pairAnswer (A₁ := A₁) (A₂ := A₂) (B₁ := B) (B₂ := B)))).comp
        (DStrategy.ofHandler (callH (E := sig1 (A₁ ⊕ A₂) (B ⊕ B)) r fun _ => foldS)) :=
  Silmaril.Proofs.Games.Abstract.SessionExt.ofHandler_routeH r

section Route

variable {E : Sig.{u}} {S₁ S₂ : Type u} {t₁ : ObsTriple E S₁ A₁ (B ⊕ PUnit.{u + 1})}
  {t₂ : ObsTriple E S₂ A₂ (B ⊕ PUnit.{u + 1})}

/-- **Two sessions side by side below the routing handler are the routed session.** -/
theorem pair_comp_routeH (r : A → A₁ ⊕ A₂) (hn₁ : NoPlainTrap t₁) (hd₁ : RetDet t₁)
    (hn₂ : NoPlainTrap t₂) (hd₂ : RetDet t₂) (s₁ : S₁) (s₂ : S₂) :
    ((threadS t₁ s₁).pair (threadS t₂ s₂)).comp (DStrategy.ofHandler (routeH r)) =
      threadS (routeS r t₁ t₂) (s₁, s₂) :=
  Silmaril.Proofs.Games.Abstract.SessionExt.pair_comp_routeH r hn₁ hd₁ hn₂ hd₂ s₁ s₂

/-- Routing keeps the absence of plain traps. -/
theorem noPlainTrap_routeS (r : A → A₁ ⊕ A₂) (hn₁ : NoPlainTrap t₁) (hn₂ : NoPlainTrap t₂) :
    NoPlainTrap (routeS r t₁ t₂) :=
  Silmaril.Proofs.Games.Abstract.SessionExt.noPlainTrap_routeS r hn₁ hn₂

/-- Routing keeps deterministic returns. -/
theorem retDet_routeS (r : A → A₁ ⊕ A₂) (hd₁ : RetDet t₁) (hd₂ : RetDet t₂) :
    RetDet (routeS r t₁ t₂) :=
  Silmaril.Proofs.Games.Abstract.SessionExt.retDet_routeS r hd₁ hd₂

end Route

/-- **Extending a session environment by a session node is a linked session**: the environment's
session serves copycat beside the node, routed by `r`. -/
theorem extS_threadS {X : Sig.{u}} {S S' : Type u} {u : ObsTriple X S' A (B ⊕ PUnit.{u + 1})}
    {t : ObsTriple (sig1 A B) S A₂ (B ⊕ PUnit.{u + 1})} (r : A → A ⊕ A₂) (hnu : NoPlainTrap u)
    (hdu : RetDet u) (hnt : NoPlainTrap t) (hdt : RetDet t) (s' : S') (s : S) :
    extS r (threadS u s') (threadS t s) =
      threadS (linkS u (routeS r idS t)) (s', (PUnit.unit, s)) :=
  Silmaril.Proofs.Games.Abstract.SessionExt.extS_threadS r hnu hdu hnt hdt s' s

end Silmaril.Games.Abstract.SessionExt
