module

public import Silmaril.Wasm.Component.DWiringLaws.Defs
public import Silmaril.Wasm.Component.DWiring.Thms
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Trap
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Inf

/-!
# Divergence and infinite plays of divergence-observing wiring: exact laws

`Silmaril.Wasm.Component.DWiring.Thms` computes the divergences of `atSizes`
up to hidden chatter below `widenH n`, and shows that such chatter plays an
eventually-trap infinite play of `σ` (`chatter_widenH`). This module closes
the gap.

**Divergence of `atSizes`.** The converse of `chatter_widenH` holds once the
infinite play is lined up with a play of the handler (`TrapChatter`): from a
position where `σ` is running, `widenH n` answers each out-of-range call with
`none` without a visible move, so the handler runs along the trap events
forever and the composite chatters (`chatter_iff`). Hence the divergences of
`widenH n` below `σ` (`div_widenH_comp`) and of `atSizes n k σ`
(`div_atSizes_iff`) are given exactly by `σ.div` and the trap chatter of
`σ`, through the handlers.

**Infinite plays of `atSizes`.** An infinite play of a composite with a handler
is an infinite play of the strategy seen through the handler, with unboundedly
many visible moves:

* below a one-call handler (`widenH n`), the strategy on top moves forever
  (`lim_t_of_oneCall`), and conversely chains lined up with an infinite play
  of `σ` form an infinite interaction: their handler side converges to an
  infinite play of the handler, and their side of `σ` to the infinite play
  itself (`inf_ofHandler_comp`, with `ThroughBelow`);
* above a handler that always calls (`AllCall`: `narrowH k`, `splitH e`), the
  strategy below moves forever when the visible play does, and conversely
  (`inf_comp_ofHandler_allCall`, with `ThroughAbove`).

Hence `inf_atSizes_iff`: the infinite plays of `atSizes n k σ` are the infinite
plays of `σ` seen through `widenH n` below and then through `narrowH k` above.
The visible moves grow without bound (as `ThroughBelow` requires); plays of
`σ` that end in trap chatter give divergences instead (above). This is the
converse of `inf_atSizes_sub`.

Proofs are in `Silmaril.Proofs.Wasm.Component.DWiringLaws`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Games.DStrategy (InfInteraction)

universe u

variable {G : Sig.{0}} {n k : Nat}

/-- **Hidden chatter below `widenH n` is exactly trap chatter of `σ`.** -/
theorem chatter_iff {σ : DStrategy sigU G} {s : List (Move (sigN n) G)} :
    (∃ i : InfInteraction (DStrategy.ofHandler (widenH n)) σ, ∀ m, i.p m = s) ↔
      TrapChatter n σ s :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.chatter_iff

namespace DStrategy

/-- **Divergence of `σ` above `widenH n`**: a divergence of `σ` seen through
the handler, or trap chatter of `σ`. -/
theorem div_widenH_comp (σ : DStrategy sigU G) :
    ((DStrategy.ofHandler (widenH n)).comp σ).div =
      {p | (∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (widenH n) ∧ v ∈ σ.div) ∨
        TrapChatter n σ p} := by
  rw [div_ofHandler_comp]
  ext p
  exact or_congr Iff.rfl chatter_iff

/-- **Divergence of `atSizes`, exactly**: a divergence of `σ`, or trap chatter
of `σ` below `widenH n`, seen through both handlers. -/
theorem div_atSizes_iff (σ : DStrategy sigU sigU) :
    (atSizes n k σ).div = {p | ∃ s t, Zip s t p ∧ t ∈ Strategy.ofHandler (narrowH k) ∧
      ((∃ u v, Zip u v s ∧ u ∈ Strategy.ofHandler (widenH n) ∧ v ∈ σ.div) ∨
        TrapChatter n σ s)} := by
  rw [div_atSizes]
  ext p
  simp only [Set.mem_ofPred_eq, chatter_iff]

end DStrategy

/-! ## Infinite plays -/

theorem allCall_narrowH (k : Nat) : AllCall (narrowH k) :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.allCall_narrowH k

theorem allCall_splitH (e : Nat) : AllCall (splitH e) :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.allCall_splitH e

namespace DStrategy

/-- **Infinite plays with a one-call handler below**: the infinite plays of
`σ` seen through the handler. -/
theorem inf_ofHandler_comp {E F G : Sig.{0}} {h : Handler E F} (hh : OneCall h)
    (σ : DStrategy F G) :
    ((DStrategy.ofHandler h).comp σ).inf = {K | ∃ I ∈ σ.inf, ThroughBelow h I K} :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.inf_ofHandler_comp hh σ

/-- **Infinite plays with a handler that always calls above**: the infinite
plays of `δ` seen through the handler. -/
theorem inf_comp_ofHandler_allCall {X E F : Sig.{u}} {h : Handler E F} (hh : AllCall h)
    (δ : DStrategy X E) :
    (δ.comp (DStrategy.ofHandler h)).inf = {J | ∃ K ∈ δ.inf, ThroughAbove h K J} :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.inf_comp_ofHandler_allCall hh δ

/-- **Infinite plays of `atSizes`, exactly**: the infinite plays of `σ` seen
through `widenH n` below and through `narrowH k` above. -/
theorem inf_atSizes_iff (σ : DStrategy sigU sigU) :
    (atSizes n k σ).inf = {J | ∃ K, (∃ I ∈ σ.inf, ThroughBelow (widenH n) I K) ∧
      ThroughAbove (narrowH k) K J} := by
  rw [atSizes, inf_comp_ofHandler_allCall (allCall_narrowH k),
    inf_ofHandler_comp (oneCall_widenH n)]
  rfl

end DStrategy

end Silmaril.Wasm.Component
