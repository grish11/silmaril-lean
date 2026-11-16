module

public import Silmaril.Games.Abstract.SessionRoute.Defs
public import Silmaril.Games.Abstract.SessionPair.Defs
public import Silmaril.Games.Abstract.SessionCat.Defs
public import Silmaril.Games.AnsMap.Defs
public import Silmaril.Games.DPair.Defs
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Defs

/-!
# Extending an environment by a session node, on session interfaces: definitions

The Wasm component denotation extends an environment `D` by a node `N` running over it, side by
side with copycat on `D`'s functions, routing each outer question to one of them
(`Silmaril.Wasm.Component.DStrategy.ext`). This module states that construction on session
interfaces, for a routing `r : A → A ⊕ A₂` of outer questions:

* `routeH r : Handler (sig1 A B ⊕ₛ sig1 A₂ B) (sig1 A B)`: the question `a` asks `r a`, on the
  copycat side (`.inl`) or on the node's side (`.inr`), and returns the answer unchanged. It is the
  one-call handler `callH r (unsum ∘ r)`.
* `extS r D N : DStrategy X (sig1 A B)`: the environment `D : DStrategy X (sig1 A B)` serving
  copycat beside the node `N : DStrategy (sig1 A B) (sig1 A₂ B)`, below `routeH r`.
* `routeS r t₁ t₂`: the session triple of `t₁` and `t₂` side by side (`StratSession.pairS`), with
  the questions routed by `r` and the answers of either side merged (`foldS`).

`pairAnswer a : (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂).Ar a → (B₁ ⊕ B₂) ⊕ PUnit` is the answer
relabelling of `StratSession.relabelPair`, as an `AnsMap` family.

Theorems in `Silmaril.Games.Abstract.SessionExt.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionExt

open Silmaril.Games Silmaril.Games.Abstract.StratObs Silmaril.Games.Abstract.StratSession
  Silmaril.Games.Abstract.SessionRoute

universe u

variable {A A₁ A₂ B B₁ B₂ : Type u}

/-- The answers of a pairing as answers of the paired session (`StratSession.pairMove`). -/
def pairAnswer :
    (a : (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂).Op) → (sig1 A₁ B₁ ⊕ₛ sig1 A₂ B₂).Ar a →
      (B₁ ⊕ B₂) ⊕ PUnit.{u + 1}
  | .inl _, x => Sum.map .inl id x
  | .inr _, x => Sum.map .inr id x

/-- An answer of either side of a pairing with common answers. -/
def unsum : (a : (sig1 A₁ B ⊕ₛ sig1 A₂ B).Op) → (sig1 A₁ B ⊕ₛ sig1 A₂ B).Ar a → B ⊕ PUnit.{u + 1}
  | .inl _, x => x
  | .inr _, x => x

/-- Merge the answers of the two sides of a paired session with common answers. -/
def foldS : (B ⊕ B) ⊕ PUnit.{u + 1} → B ⊕ PUnit.{u + 1} := Sum.map (Sum.elim id id) id

/-- **The routing handler**: ask `r a` on its side, return the answer. -/
def routeH (r : A → A₁ ⊕ A₂) : Handler (sig1 A₁ B ⊕ₛ sig1 A₂ B) (sig1 A B) :=
  callH r fun a => unsum (r a)

/-- **Extend the environment `D` by the node `N`**, side by side with copycat on `D`'s functions,
outer questions routed by `r`. -/
def extS {X : Sig.{u}} (r : A → A ⊕ A₂) (D : DStrategy X (sig1 A B))
    (N : DStrategy (sig1 A B) (sig1 A₂ B)) : DStrategy X (sig1 A B) :=
  D.comp (((DStrategy.id (sig1 A B)).pair N).comp (DStrategy.ofHandler (routeH r)))

/-- **Two session triples side by side, routed**: the question `a` is a round of the side of
`r a`; the answers of both sides are merged. -/
def routeS {E : Sig.{u}} {S₁ S₂ : Type u} (r : A → A₁ ⊕ A₂)
    (t₁ : ObsTriple E S₁ A₁ (B ⊕ PUnit.{u + 1})) (t₂ : ObsTriple E S₂ A₂ (B ⊕ PUnit.{u + 1})) :
    ObsTriple E (S₁ × S₂) A (B ⊕ PUnit.{u + 1}) :=
  mapS r (fun _ => foldS) (pairS t₁ t₂)

end Silmaril.Games.Abstract.SessionExt
