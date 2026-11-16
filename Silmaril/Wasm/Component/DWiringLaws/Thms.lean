module

public import Silmaril.Wasm.Component.DWiringLaws.Defs
public import Silmaril.Wasm.Component.DWiring.Thms
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Trap

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

Proofs are in `Silmaril.Proofs.Wasm.Component.DWiringLaws`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games
open Silmaril.Games.DStrategy (InfInteraction)

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

end Silmaril.Wasm.Component
