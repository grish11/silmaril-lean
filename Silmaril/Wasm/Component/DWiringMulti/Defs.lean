module

public import Silmaril.Wasm.Component.DWiringChatter3.Defs

/-!
# Divergence and infinite plays of a multi-node component: definitions

`denNodesD C e ns D` extends the environment `D` by the nodes `ns`, one
`DStrategy.ext` at a time. The laws of `ext` (`div_ext_eq_routed`,
`inf_ext_routed`) give the divergences and infinite plays of `ext e D N` from
three observations of `D`, its finite plays, its divergences and its infinite
plays, and the same three of the node `N`. This module names those
observations and the step on them, so that the divergences and infinite plays
of a component with any number of nodes are a fold over its nodes
(`Silmaril.Wasm.Component.DWiringMulti.Thms`).

* `DObs X`: finite plays, divergences and infinite plays of an environment
  over `X`; `DObs.of D` those of `D`. `DObs.IsRun d I`: `I` is an
  infinite play, or the prefixes of a finite play (`IsRun`).
* The three sources of divergence of `ext e D N`:
  - `EnvDiv e S N`: a divergence `s ∈ S` of the environment, seen through a
    play of the node layer `extTop e N` above it (the environment's own
    divergence, routed one node further up);
  - `NodeDiv e P N`: a divergence of `N` itself, on `N`'s half of the
    pairing below `splitH e`, above a play of the environment in `P`;
  - `NodeChatter e K N`: an infinite play of the environment (in `K`) and an
    infinite play of `N` exchanging moves forever (`ExtChatter`).
* `ExtInf e d N`: the infinite plays of `ext e D N` (`inf_ext_routed`).
* `DObs.ext e d N`: the observations of `ext e D N` from those of `D`.
* `nodesObs C e ns d`: the fold of `DObs.ext` along the nodes, as `denNodesD`.
* `firstObs e N`: the observations of the first node above `maskH e` when it
  propagates traps: `maskH` neither diverges nor chatters with it, so its only
  divergences are its own.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

/-- **The observations of an environment over `X`**: its finite plays, its
divergences and its infinite plays. -/
structure DObs (X : Sig.{0}) where
  /-- The finite plays. -/
  plays : Strategy X sigU
  /-- The divergences. -/
  div : Set (List (Move X sigU))
  /-- The infinite plays. -/
  inf : Set (Set (List (Move X sigU)))

/-- The observations of a divergence-observing environment. -/
def DObs.of {X : Sig.{0}} (D : DStrategy X sigU) : DObs X := ⟨D.toStrategy, D.div, D.inf⟩

variable {X : Sig.{0}}

/-- A run of the observed environment: an infinite play, or the prefixes of a
finite play (as `IsRun`). -/
def DObs.IsRun (d : DObs X) (I : Set (List (Move X sigU))) : Prop :=
  I ∈ d.inf ∨ ∃ s₀ ∈ d.plays, I = prefixes s₀

/-- **A divergence of the environment, one node further up**: a divergence in
`S`, seen through a play of the node layer `extTop e N`. -/
def EnvDiv (e : Nat) (S : Set (List (Move X sigU))) (N : DStrategy sigU sigU) :
    Set (List (Move X sigU)) :=
  {p | ∃ s t, Zip s t p ∧ s ∈ S ∧ t ∈ (DStrategy.extTop e N).toStrategy}

/-- **A divergence of the node itself**: `N` diverges on its half of the
pairing below `splitH e`, above a play of the environment in `P`. -/
def NodeDiv (e : Nat) (P : Strategy X sigU) (N : DStrategy sigU sigU) :
    Set (List (Move X sigU)) :=
  {p | ∃ s t, Zip s t p ∧ s ∈ P ∧ ∃ a b, Zip a b t ∧
    (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
      b ∈ Strategy.ofHandler (splitH e)}

/-- **Chatter between the environment and the node**: an infinite play of the
environment (in `K`) and an infinite play of `N` exchanging moves forever,
routed by `splitH e` (`ExtChatter`). -/
def NodeChatter (e : Nat) (K : Set (Set (List (Move X sigU)))) (N : DStrategy sigU sigU) :
    Set (List (Move X sigU)) :=
  {p | ∃ I ∈ K, ∃ L ∈ N.inf, ExtChatter e I L p}

/-- **The infinite plays of `ext e D N`**, from the observations `d` of `D`:
an infinite trace interleaving a run of `D` with a trace above it of legal plays
routed by `splitH e` to plays of copycat beside `N`, whose half of `N`, when
infinite, is an infinite play of `N` (`inf_ext_routed`). -/
def ExtInf (e : Nat) (d : DObs X) (N : DStrategy sigU sigU) : Set (Set (List (Move X sigU))) :=
  {J | IsInfPlay J ∧ ∃ I C, d.IsRun I ∧
    (IsInfPlay C ∨ ∃ c₀, C = prefixes c₀) ∧
    (∀ c ∈ C, Legal c ∧ c.map (splitRoute e) ∈ (Strategy.id sigU).pair N.toStrategy) ∧
    (IsInfPlay (Split.infR (List.map (splitRoute e) '' C)) →
      Split.infR (List.map (splitRoute e) '' C) ∈ N.inf) ∧
    Interleaved I C J}

/-- **One node more**: the observations of `ext e D N` from the observations
`d` of `D`. Divergences are the environment's routed one node up, the node's
own, and chatter between the two. -/
def DObs.ext (e : Nat) (d : DObs X) (N : DStrategy sigU sigU) : DObs X where
  plays := Component.ext e d.plays N.toStrategy
  div := EnvDiv e d.div N ∪ NodeDiv e d.plays N ∪ NodeChatter e d.inf N
  inf := ExtInf e d N

variable {M : Type} [CoreModule M]

/-- **The observations after the nodes `ns`**: `DObs.ext` along the nodes, as
`denNodesD`. -/
def nodesObs (C : DCoreSem M) : Nat → List (Node M) → DObs X → DObs X
  | _, [], d => d
  | e, n :: ns, d => nodesObs C (e + n.width) ns (d.ext e (Node.denD C e n))

/-- **The first node above `maskH e`, when it propagates traps**: the
observations of `ext e (ofHandler (maskH e)) N`, whose divergences are only the
node's own. -/
def firstObs (e : Nat) (N : DStrategy sigU sigU) : DObs sigU where
  plays := Component.ext e (Strategy.ofHandler (maskH e)) N.toStrategy
  div := NodeDiv e (Strategy.ofHandler (maskH e)) N
  inf := ExtInf e (DObs.of (DStrategy.ofHandler (maskH e))) N

end Silmaril.Wasm.Component
