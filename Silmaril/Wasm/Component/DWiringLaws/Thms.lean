module

public import Silmaril.Wasm.Component.DWiringLaws.Defs
public import Silmaril.Wasm.Component.DWiring.Thms
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Trap
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Inf
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Ext
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Silent
import Silmaril.Proofs.Wasm.Component.DWiringLaws.Impls

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

**`ext`.** `ext e D N = D.comp (extTop e N)`, where `extTop e N` is copycat
beside `N` below `splitH e`. In the pairing, copycat neither diverges nor
constrains infinite plays (`div_pair_id`, `inf_pair_id`). `splitH e` is a
one-call handler that always calls, so `extTop e N` has no hidden chatter: it
diverges exactly where `N` does, on the right half of the pairing play
(`div_extTop`), and its infinite plays are the infinite plays of the pairing
seen through `splitH e` (`inf_extTop`). The divergences of `ext e D N` are
those of `D`, those of `N`, and hidden chatter between `D` and `N`
(`div_ext`); its infinite plays are the visible limits of its infinite
interactions (`inf_ext`).

**Any handler below.** The argument for `widenH` works for every handler:
hidden chatter of a handler `h` with `σ` is exactly silent chatter
(`chatter_iff_silent`), an infinite play of `σ` that from a running position
consists of questions `h` answers without a call and their answers
(`SilentChatter`). Hence `div_ofHandler_comp_iff`.

**The component denotation, layer by layer.** The wiring handlers `implsH`,
`implsN`, `exportsH` and `maskH` make at most one call (`oneCall_implsH`, …),
so above a strategy they add no chatter, and below one they add exactly silent
chatter. Each constructor of `Comp.denD` therefore has an exact divergence law
in terms of the divergences and infinite plays of its parts: `div_denD`
(trap chatter below `widenH`), `div_denUD` (no chatter below `exportsH`),
`div_ext_ofHandler` (the first node, above `maskH`), `div_ext` (later nodes),
`div_dcoreNode` (silent chatter of a core module with `implsN` below, no
chatter below `widenH`) and `div_node_inst`. The one clause these laws do not
reduce further is the hidden chatter between an environment that is not a
handler and the node above it (`InfInteraction D (extTop e N)` in `div_ext`):
two instances calling each other forever.

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

/-! ## `ext` -/

/-- Copycat beside `N` diverges exactly where `N` does, on the right half. -/
theorem div_pair_id {E F : Sig.{u}} (N : DStrategy E F) :
    ((DStrategy.id E).pair N).div =
      {a | a ∈ (Strategy.id E).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div} :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.div_pair_id N

/-- The infinite plays of copycat beside `N`: only the right projection is
constrained. -/
theorem inf_pair_id {E F : Sig.{u}} (N : DStrategy E F) :
    ((DStrategy.id E).pair N).inf =
      {K | IsInfPlay K ∧ K ⊆ ((Strategy.id E).pair N.toStrategy).plays ∧
        (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf)} :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.inf_pair_id N

/-- `ext` is `D` below `extTop`. -/
theorem ext_eq_comp {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    ext e D N = D.comp (extTop e N) := rfl

/-- **Divergence above the environment**: no chatter below `splitH e`; a
divergence of `N` on the right half of the pairing play. -/
theorem div_extTop (e : Nat) (N : DStrategy sigU sigU) :
    (extTop e N).div = {p | ∃ a b, Zip a b p ∧
      (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
        b ∈ Strategy.ofHandler (splitH e)} := by
  rw [extTop, div_comp_ofHandler (oneCall_splitH e), div_pair_id]
  rfl

/-- **Infinite plays above the environment**: infinite plays of copycat beside
`N`, seen through `splitH e`. -/
theorem inf_extTop (e : Nat) (N : DStrategy sigU sigU) :
    (extTop e N).inf = {J | ∃ K, (IsInfPlay K ∧
      K ⊆ ((Strategy.id sigU).pair N.toStrategy).plays ∧
        (IsInfPlay (Split.infR K) → Split.infR K ∈ N.inf)) ∧ ThroughAbove (splitH e) K J} := by
  rw [extTop, inf_comp_ofHandler_allCall (allCall_splitH e), inf_pair_id]
  rfl

/-- **Divergence of `ext`**: a divergence of `D`, a divergence of `N` through
the pairing and `splitH e`, or hidden chatter between `D` and `extTop e N`. -/
theorem div_ext {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (ext e D N).div =
      {p | ∃ s t, Zip s t p ∧ ((s ∈ D.div ∧ t ∈ (extTop e N).toStrategy) ∨
        (s ∈ D.toStrategy ∧ ∃ a b, Zip a b t ∧
          (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
            b ∈ Strategy.ofHandler (splitH e)))} ∪
      {p | ∃ i : InfInteraction D (extTop e N), ∀ m, i.p m = p} := by
  ext p
  rw [ext_eq_comp, Silmaril.Games.DStrategy.mem_div_comp, div_extTop]
  rfl

/-- **Infinite plays of `ext`**: the visible limits of the infinite
interactions of `D` with `extTop e N` whose visible part grows forever. -/
theorem inf_ext {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (ext e D N).inf =
      {I | ∃ i : InfInteraction D (extTop e N), i.p.Unbounded ∧ I = i.p.lim} := rfl

end DStrategy

/-! ## Any handler below -/

/-- **Hidden chatter below a handler is exactly silent chatter.** -/
theorem chatter_iff_silent {E F G : Sig.{u}} {h : Handler E F} {σ : DStrategy F G}
    {s : List (Move E G)} :
    (∃ i : InfInteraction (DStrategy.ofHandler h) σ, ∀ m, i.p m = s) ↔ SilentChatter h σ s :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.chatter_iff_silent

namespace DStrategy

/-- **Divergence with a handler below, exactly**: a divergence of `σ` through
the handler, or silent chatter of `σ`. -/
theorem div_ofHandler_comp_iff {E F G : Sig.{u}} (h : Handler E F) (σ : DStrategy F G) :
    ((DStrategy.ofHandler h).comp σ).div =
      {p | (∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler h ∧ v ∈ σ.div) ∨ SilentChatter h σ p} :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.div_ofHandler_comp_iff h σ

end DStrategy

/-! ## The component denotation, layer by layer -/

theorem oneCall_implsH (e : Nat) (ims : List Impl) : OneCall (implsH e ims) :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.oneCall_implsH e ims

theorem oneCall_implsN (e : Nat) (ims : List Impl) (t : Nat) : OneCall (implsN e ims t) :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.oneCall_implsN e ims t

theorem oneCall_exportsH (e : Nat) (xs : List Export) : OneCall (exportsH e xs) :=
  oneCall_implsH e _

theorem oneCall_maskH (e : Nat) : OneCall (maskH e) :=
  Silmaril.Proofs.Wasm.Component.DWiringLaws.oneCall_maskH e

variable {M : Type} [CoreModule M]

/-- **Divergence of a component**: a divergence of its denotation over `sigU`,
or trap chatter of it below `widenH`, through the interface handlers. -/
theorem div_denD (C : DCoreSem M) (c : Comp M) :
    (c.denD C).div = {p | ∃ s t, Zip s t p ∧ t ∈ Strategy.ofHandler (narrowH c.exports.length) ∧
      ((∃ u v, Zip u v s ∧ u ∈ Strategy.ofHandler (widenH c.imports.length) ∧
        v ∈ (c.denUD C).div) ∨ TrapChatter c.imports.length (c.denUD C) s)} :=
  DStrategy.div_atSizes_iff _

/-- **Divergence over `sigU`**: no chatter below `exportsH`; a divergence of
the environment built by the nodes. -/
theorem div_denUD (C : DCoreSem M) (I : Iface) (ns : List (Node M)) (xs : List Export) :
    (Comp.denUD C (.mk I ns xs)).div = {p | ∃ s t, Zip s t p ∧
      s ∈ (denNodesD C I.length ns (DStrategy.ofHandler (maskH I.length))).div ∧
        t ∈ Strategy.ofHandler (exportsH (envAfter I.length ns) xs)} := by
  rw [Comp.denUD]
  exact DStrategy.div_comp_ofHandler (oneCall_exportsH _ _) _

/-- Extending the environment by no node. -/
theorem denNodesD_nil (C : DCoreSem M) {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU) :
    denNodesD C e [] D = D := by
  rw [denNodesD]

/-- Extending the environment by a node, then the others. -/
theorem denNodesD_cons (C : DCoreSem M) {X : Sig.{0}} (e : Nat) (n : Node M) (ns : List (Node M))
    (D : DStrategy X sigU) :
    denNodesD C e (n :: ns) D =
      denNodesD C (e + n.width) ns (DStrategy.ext e D (Node.denD C e n)) := by
  rw [denNodesD]

/-- **Divergence of the first node above a handler** (`maskH` for a
component): a divergence of the node through `splitH`, or silent chatter of
the node above the handler. -/
theorem div_ext_ofHandler (e : Nat) (h : Handler sigU sigU) (N : DStrategy sigU sigU) :
    (DStrategy.ext e (DStrategy.ofHandler h) N).div = {p |
      (∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler h ∧ ∃ a b, Zip a b v ∧
        (a ∈ (Strategy.id sigU).pair N.toStrategy ∧ (Split.halves false a).2 ∈ N.div) ∧
          b ∈ Strategy.ofHandler (splitH e)) ∨ SilentChatter h (DStrategy.extTop e N) p} := by
  rw [DStrategy.ext_eq_comp, DStrategy.div_ofHandler_comp_iff, DStrategy.div_extTop]
  rfl

/-- **Divergence of a core instance**: a divergence of the core module through
`implsN` below and `widenH` above (which adds no chatter), or silent chatter of
the module, seen through `widenH`, above `implsN`. -/
theorem div_dcoreNode (C : DCoreSem M) (e : Nat) (m : M) (args : List Impl) :
    (dcoreNode C e m args).div = {p |
      (∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (implsN e args (CoreModule.imports m).length) ∧
        ∃ a b, Zip a b v ∧ a ∈ (C.sem m).div ∧
          b ∈ Strategy.ofHandler (widenH (CoreModule.exports m).length)) ∨
      SilentChatter (implsN e args (CoreModule.imports m).length)
        ((C.sem m).comp (DStrategy.ofHandler (widenH (CoreModule.exports m).length))) p} := by
  rw [dcoreNode, DStrategy.div_ofHandler_comp_iff,
    DStrategy.div_comp_ofHandler (oneCall_widenH _)]
  rfl

/-- **Divergence of a component instance**: a divergence of the component over
`sigU` through `implsH`, or silent chatter of it above `implsH`. -/
theorem div_node_inst (C : DCoreSem M) (e : Nat) (c : Comp M) (args : List Impl) :
    (Node.denD C e (.inst c args)).div = {p |
      (∃ u v, Zip u v p ∧ u ∈ Strategy.ofHandler (implsH e args) ∧ v ∈ (c.denUD C).div) ∨
        SilentChatter (implsH e args) (c.denUD C) p} := by
  rw [Node.denD]
  exact DStrategy.div_ofHandler_comp_iff _ _

end Silmaril.Wasm.Component
