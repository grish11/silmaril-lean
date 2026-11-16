module

public import Silmaril.Wasm.Component.DWiringChatter2.Defs
public import Silmaril.Wasm.Component.DWiringChatter.Thms
import Silmaril.Proofs.Wasm.Component.DWiringChatter2.Ext

/-!
# Chatter between an environment and the node above it, routed

`Silmaril.Wasm.Component.DWiringChatter.Thms` puts hidden chatter between `D`
and `extTop e N` in terms of an infinite play `K` of copycat beside `N`, seen
through `splitH e` (`chatter_extTop_iff`). This module eliminates `K` and the
`ThroughAbove` limit: chatter is an infinite play `I` of `D` and an infinite
play `L` of `N` exchanging moves forever, after a finite prefix routed by
`splitH e` (`chatter_ext_iff`, with `ExtChatter`).

* **Chatter is eventually pure synchronisation** (`chatter_iff_tail`): two
  infinite traces chatter after `p` iff, after an aligned pair interacting with
  visible part `p`, they continue by the same shared events forever. Only
  finitely many outer events fit into the fixed visible part `p`.
* **The routing of `splitH e`** (`splitRoute`): the pairing play under a play
  `c` above `D` is `c.map (splitRoute e)`, up to an outer question not yet
  forwarded (`splitRoute_prefix_of_zip`), and every legal `c` arises so
  (`exists_zip_splitRoute`). Moves at `D`'s interface are then split between
  copycat and `N` by the round in progress (`Split.halves`).
* **Copycat is eventually silent** (`copycat_silent_extTop`): in the closed
  form of `chatter_extTop_iff`, copycat's projection of `K` is bounded and
  `N`'s is infinite. Copycat moves at `D`'s interface only to pass on outer
  moves, at most one more than it receives from outside, and outer moves are
  part of the fixed visible play. So the round in progress after the visible
  prefix is `N`'s, and the remaining moves are `N`'s calls to `D` and `D`'s
  answers. When copycat's projection is infinite, `D`'s imports are passed
  outward forever and the visible play grows; that is an infinite play of
  `ext e D N`, not a divergence.
* Hence `chatter_ext_iff` and the divergences of `ext e D N` in terms of `D`
  and `N` alone, without limits of the pairing (`div_ext_eq_routed`).

Proofs are in `Silmaril.Proofs.Wasm.Component.DWiringChatter2`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Games.DStrategy (InfInteraction)

universe u v w

/-- **Chatter is eventually pure synchronisation.** Two infinite traces chatter
after `p` iff, after an aligned pair `s₀ ∈ I`, `c₀ ∈ J` interacting with
visible part `p`, both continue by the same arbitrarily long shared events. -/
theorem chatter_iff_tail {α : Type u} {β : Type v} {γ : Type w} {I : Set (List (α ⊕ β))}
    {J : Set (List (β ⊕ γ))} (hI : IsInfPlay I) (hJ : IsInfPlay J) {p : List (α ⊕ γ)} :
    Chatter I J p ↔ ∃ s₀ ∈ I, ∃ c₀ ∈ J, Zip s₀ c₀ p ∧
      ∀ k, ∃ w : List β, k ≤ w.length ∧ s₀ ++ w.map .inr ∈ I ∧ c₀ ++ w.map .inl ∈ J :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter2.chatter_tail_iff hI hJ

/-! ## Plays through `splitH` -/

/-- **The pairing play under a play through `splitH e`**: `c.map (splitRoute e)`
is a prefix of it, unless `c` ends with an outer question not yet forwarded. -/
theorem splitRoute_prefix_of_zip {e : Nat} {a : List (Move sigU (sigU ⊕ₛ sigU))}
    {w : List (Move (sigU ⊕ₛ sigU) sigU)} {c : List (Move sigU sigU)} (hz : Zip a w c)
    (hw : w ∈ Strategy.ofHandler (splitH e)) (ha : Legal a) :
    c.map (splitRoute e) <+: a ∨ ∃ c' q, c = c' ++ [.inr (.ask q)] :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter2.route_prefix_of_zip hz hw ha

/-- **Every legal play is served by `splitH e`** from its routed pairing play. -/
theorem exists_zip_splitRoute {e : Nat} {c : List (Move sigU sigU)} (h : Legal c) :
    ∃ w ∈ Strategy.ofHandler (splitH e), Zip (c.map (splitRoute e)) w c :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter2.exists_zip_route h

/-- Routing preserves legality. -/
theorem legal_splitRoute {e : Nat} {c : List (Move sigU sigU)} (h : Legal c) :
    Legal (c.map (splitRoute e)) :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter2.legal_route h

namespace DStrategy

variable {X : Sig.{0}} {e : Nat} {D : DStrategy X sigU} {N : DStrategy sigU sigU}
  {p : List (Move X sigU)}

/-- **Copycat is eventually silent.** In the closed form of
`chatter_extTop_iff`, copycat's projection of the pairing play `K` is bounded,
and `N`'s is an infinite trace (hence an infinite play of `N`). -/
theorem copycat_silent_extTop {I : Set (List (Move X sigU))} (hI : I ∈ D.inf)
    {K : Set (List (Move sigU (sigU ⊕ₛ sigU)))}
    (hK : IsInfPlay K ∧ K ⊆ ((Strategy.id sigU).pair N.toStrategy).plays ∧
      (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf))
    {J : Set (List (Move sigU sigU))} (hTA : ThroughAbove (splitH e) K J) (hC : Chatter I J p) :
    ¬ IsInfPlay (Split.infL K) ∧ IsInfPlay (Split.infR K) :=
  Silmaril.Proofs.Wasm.Component.DWiringChatter2.copycat_silent hI hK hTA hC

/-- **Chatter between an environment and the node above it, routed**: an
infinite play `I` of `D` and an infinite play `L` of `N` exchanging moves
forever after a finite prefix routed by `splitH e`, with copycat silent and the
outer moves constant (`ExtChatter`). -/
theorem chatter_ext_iff :
    (∃ i : InfInteraction D (extTop e N), ∀ m, i.p m = p) ↔
      ∃ I ∈ D.inf, ∃ L ∈ N.inf, ExtChatter e I L p :=
  ⟨Silmaril.Proofs.Wasm.Component.DWiringChatter2.extChatter_of_chatter,
    fun ⟨_, hI, _, hL, h⟩ =>
      Silmaril.Proofs.Wasm.Component.DWiringChatter2.chatter_of_extChatter hI hL h⟩

/-- **Divergence of `ext`, in terms of `D` and `N`, routed**: a divergence of
`D`, a divergence of `N` through the pairing and `splitH e`, or `D` and `N`
exchanging moves forever (`ExtChatter`). -/
theorem div_ext_eq_routed (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (ext e D N).div =
      {p | ∃ s t, Zip s t p ∧ ((s ∈ D.div ∧ t ∈ (extTop e N).toStrategy) ∨
        (s ∈ D.toStrategy ∧ ∃ a b, Zip a b t ∧
          (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
            b ∈ Strategy.ofHandler (splitH e)))} ∪
      {p | ∃ I ∈ D.inf, ∃ L ∈ N.inf, ExtChatter e I L p} := by
  rw [div_ext]
  ext p
  exact or_congr Iff.rfl chatter_ext_iff

end DStrategy

end Silmaril.Wasm.Component
