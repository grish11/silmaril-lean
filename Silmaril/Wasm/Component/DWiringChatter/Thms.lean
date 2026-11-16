module

public import Silmaril.Wasm.Component.DWiringLaws.Thms
public import Silmaril.Games.DivCompChatter.Thms

/-!
# Hidden chatter between an environment and the node above it

`Silmaril.Wasm.Component.DWiringLaws.Thms` computes the divergences of
`ext e D N = D.comp (extTop e N)` up to one clause: hidden chatter
`InfInteraction D (extTop e N)` between the environment `D` and the node `N`
above it (`div_ext`). This module puts that clause in closed form, using the
characterisation of chatter by infinite plays (`InfInteraction.chatter_iff`
in `Silmaril.Games.DivCompChatter.Thms`).

* Below a handler `h` that always calls (`AllCall`), chatter of `σ` with
  `δ.comp (ofHandler h)` is an infinite play `I` of `σ` chattering with an
  infinite play `K` of `δ` seen through `h`
  (`chatter_comp_ofHandler_allCall_iff`).
* For `extTop e N`, `δ` is copycat beside `N` and `h = splitH e`: chatter of
  `D` with `extTop e N` is an infinite play of `D` chattering with an infinite
  play of the pairing, constrained by `N.inf` on its right half, seen through
  `splitH e` (`chatter_extTop_iff`).
* Hence the divergences of `ext e D N` in terms of `D` and `N` alone
  (`div_ext_eq`).
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Games.DStrategy (InfInteraction)

universe u

namespace DStrategy

/-- **Chatter through a handler that always calls**: an infinite play of `σ`
chattering with an infinite play of `δ` seen through `h`. -/
theorem chatter_comp_ofHandler_allCall_iff {W X E F : Sig.{u}} {h : Handler E F}
    (hh : AllCall h) {σ : DStrategy W X} {δ : DStrategy X E} {p : List (Move W F)} :
    (∃ i : InfInteraction σ (δ.comp (Games.DStrategy.ofHandler h)), ∀ m, i.p m = p) ↔
      ∃ I ∈ σ.inf, ∃ K ∈ δ.inf, ∃ J, ThroughAbove h K J ∧ Chatter I J p := by
  rw [Games.DStrategy.InfInteraction.chatter_iff, inf_comp_ofHandler_allCall hh]
  exact ⟨fun ⟨I, hI, J, ⟨K, hK, hJ⟩, hc⟩ => ⟨I, hI, K, hK, J, hJ, hc⟩,
    fun ⟨I, hI, K, hK, J, hJ, hc⟩ => ⟨I, hI, J, ⟨K, hK, hJ⟩, hc⟩⟩

/-- **Chatter between an environment and the node above it**, in closed form:
an infinite play `I` of `D` chattering with an infinite play of copycat beside
`N` (whose right half, when infinite, is an infinite play of `N`) seen through
`splitH e`. -/
theorem chatter_extTop_iff {X : Sig.{0}} {e : Nat} {D : DStrategy X sigU}
    {N : DStrategy sigU sigU} {p : List (Move X sigU)} :
    (∃ i : InfInteraction D (extTop e N), ∀ m, i.p m = p) ↔
      ∃ I ∈ D.inf, ∃ K, (IsInfPlay K ∧ K ⊆ ((Strategy.id sigU).pair N.toStrategy).plays ∧
        (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf)) ∧
          ∃ J, ThroughAbove (splitH e) K J ∧ Chatter I J p := by
  rw [extTop, chatter_comp_ofHandler_allCall_iff (allCall_splitH e), inf_pair_id]
  exact Iff.rfl

/-- **Divergence of `ext`, in terms of `D` and `N`**: a divergence of `D`, a
divergence of `N` through the pairing and `splitH e`, or an infinite play of
`D` chattering with an infinite play of copycat beside `N` seen through
`splitH e`. -/
theorem div_ext_eq {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (ext e D N).div =
      {p | ∃ s t, Zip s t p ∧ ((s ∈ D.div ∧ t ∈ (extTop e N).toStrategy) ∨
        (s ∈ D.toStrategy ∧ ∃ a b, Zip a b t ∧
          (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
            b ∈ Strategy.ofHandler (splitH e)))} ∪
      {p | ∃ I ∈ D.inf, ∃ K, (IsInfPlay K ∧ K ⊆ ((Strategy.id sigU).pair N.toStrategy).plays ∧
        (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf)) ∧
          ∃ J, ThroughAbove (splitH e) K J ∧ Chatter I J p} := by
  rw [div_ext]
  ext p
  exact or_congr Iff.rfl chatter_extTop_iff

end DStrategy

end Silmaril.Wasm.Component
