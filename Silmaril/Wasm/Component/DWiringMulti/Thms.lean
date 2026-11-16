module

public import Silmaril.Wasm.Component.DWiringMulti.Defs
public import Silmaril.Wasm.Component.DWiringChatter3.Thms
public import Silmaril.Wasm.Component.OutOfRange.Thms
import Silmaril.Proofs.Wasm.Component.DWiringMulti.Fold

/-!
# Divergence and infinite plays of a multi-node component

`Silmaril.Wasm.Component.OutOfRange.Thms` gives the divergences of a component
with one node (`div_denD_single`). This module gives them, and the infinite
plays, for any number of nodes, by induction on `denNodesD`.

**One node more** (`obs_ext`). The laws of `ext` (`div_ext_eq_routed`,
`inf_ext_routed`) depend on the environment `D` only through its finite plays,
divergences and infinite plays (`DObs.of D`). So the observations of
`ext e D N` are a function of those of `D` and of `N`, `DObs.ext`:

* finite plays: `Component.ext e D.toStrategy N.toStrategy`;
* divergences (`div_ext_sources`), from three sources:
  - (`EnvDiv`) a divergence of `D`, routed through a play of the node layer
    `extTop e N` above it;
  - (`NodeDiv`) a divergence of `N` itself, on its half of the pairing below
    `splitH e`, above a finite play of `D`;
  - (`NodeChatter`) **chatter**: an infinite play of `D` and an infinite play
    of `N` exchanging moves forever with nothing visible (`ExtChatter`), that is,
    mutual recursion between the environment so far and the node;
* infinite plays (`ExtInf`): a run of `D` interleaved with a trace of legal
  plays routed by `splitH e` to copycat beside `N`, constrained by `N.inf`.

**All the nodes** (`obs_denNodesD`). Hence the observations of the environment
after the nodes `ns` are the fold `nodesObs` of `DObs.ext` along the nodes:
`DObs.of (denNodesD C e ns D) = nodesObs C e ns (DObs.of D)`. Unfolding the fold,
a divergence of the final environment is a node's own divergence (`NodeDiv`) or
chatter between the environment so far and a node (`NodeChatter`), arising at
some node and routed (`EnvDiv`) through the node layers above it; or a
divergence of the starting environment, routed through all of them. Infinite
plays are given by the same fold, so the chatter clause at each node refers to
the infinite plays of the environment so far in closed form.

**The component** (`div_denD_nodes`, `inf_denD_nodes`). The starting
environment is `maskH I.length`, which does not diverge; the outer layers
(`exportsH`, `widenH`, `narrowH`) add no divergence (`div_denUD`,
`div_denD_eq`, unconditionally). So the divergences of a component are the
divergences of `nodesObs` through the outer handlers, with no hypothesis.

**Under trap propagation** (`div_denD_multi`). The one place where the wiring
itself could add a divergence is chatter between `maskH` and the first node: the
node calling an out-of-range import forever, answered `none`. When the first
node propagates traps, there is none (`div_ext_maskH`), and the environment
after the first node has only the node's own divergences (`firstObs`,
`obs_ext_maskH`). Then every divergence of the component is (a) a node's own
divergence, or (b) chatter between the environment so far and a later node,
routed through the wiring. Only the first node's trap propagation is needed:
the chatter of later nodes is with the environment built by earlier nodes, not
with a handler, and is genuine mutual recursion
(`div_denD_multi_of_forall` states the form with every node propagating traps).

Proofs are in `Silmaril.Proofs.Wasm.Component.DWiringMulti`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

variable {X : Sig.{0}}

/-! ## One node more -/

/-- **The three sources of divergence of `ext`**: the environment's own,
routed one node up; the node's own; chatter between the two. -/
theorem div_ext_sources (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    (DStrategy.ext e D N).div =
      EnvDiv e D.div N ∪ NodeDiv e D.toStrategy N ∪ NodeChatter e D.inf N :=
  Silmaril.Proofs.Wasm.Component.DWiringMulti.div_ext e D N

/-- **The observations of `ext e D N` are a function of those of `D` and `N`.** -/
theorem obs_ext (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    DObs.of (DStrategy.ext e D N) = (DObs.of D).ext e N :=
  Silmaril.Proofs.Wasm.Component.DWiringMulti.obs_ext e D N

/-- **The first node above `maskH`, under trap propagation**: only the node's
own divergences. -/
theorem obs_ext_maskH (e : Nat) {N : DStrategy sigU sigU} (hN : TrapPropagating N) :
    DObs.of (DStrategy.ext e (DStrategy.ofHandler (maskH e)) N) = firstObs e N :=
  Silmaril.Proofs.Wasm.Component.DWiringMulti.obs_ext_maskH e hN

/-! ## All the nodes -/

variable {M : Type} [CoreModule M]

/-- **The environment after the nodes is the fold of `DObs.ext`.** -/
theorem obs_denNodesD (C : DCoreSem M) (e : Nat) (ns : List (Node M)) (D : DStrategy X sigU) :
    DObs.of (denNodesD C e ns D) = nodesObs C e ns (DObs.of D) :=
  Silmaril.Proofs.Wasm.Component.DWiringMulti.obs_denNodesD C e ns D

/-- **Divergences of the environment after the nodes.** -/
theorem div_denNodesD (C : DCoreSem M) (e : Nat) (ns : List (Node M)) (D : DStrategy X sigU) :
    (denNodesD C e ns D).div = (nodesObs C e ns (DObs.of D)).div :=
  congrArg DObs.div (obs_denNodesD C e ns D)

/-- **Infinite plays of the environment after the nodes.** -/
theorem inf_denNodesD (C : DCoreSem M) (e : Nat) (ns : List (Node M)) (D : DStrategy X sigU) :
    (denNodesD C e ns D).inf = (nodesObs C e ns (DObs.of D)).inf :=
  congrArg DObs.inf (obs_denNodesD C e ns D)

/-- `nodesObs` on no node. -/
@[simp] theorem nodesObs_nil (C : DCoreSem M) (e : Nat) (d : DObs X) :
    nodesObs C e [] d = d := by
  rw [nodesObs]

/-- `nodesObs` on a node, then the others. -/
theorem nodesObs_cons (C : DCoreSem M) (e : Nat) (n : Node M) (ns : List (Node M))
    (d : DObs X) :
    nodesObs C e (n :: ns) d = nodesObs C (e + n.width) ns (d.ext e (Node.denD C e n)) := by
  rw [nodesObs]

/-! ## The component -/

/-- **Divergence of a component with any number of nodes**, with no
hypothesis: the divergences of the fold `nodesObs` from `maskH`, through the
outer handlers `exportsH`, `widenH` and `narrowH`. -/
theorem div_denD_nodes (C : DCoreSem M) (I : Iface) (ns : List (Node M)) (xs : List Export) :
    ((Comp.mk I ns xs).denD C).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH I.length) ∧
        t ∈ Strategy.ofHandler (narrowH xs.length) ∧ ∃ d x, Zip d x v ∧
          d ∈ (nodesObs C I.length ns (DObs.of (DStrategy.ofHandler (maskH I.length)))).div ∧
          x ∈ Strategy.ofHandler (exportsH (envAfter I.length ns) xs)} := by
  rw [div_denD_eq, div_denUD, div_denNodesD]
  rfl

/-- **A component without nodes does not diverge.** -/
theorem div_denD_nil (C : DCoreSem M) (I : Iface) (xs : List Export) :
    ((Comp.mk I [] xs).denD C).div = ∅ := by
  rw [div_denD_nodes]
  exact Set.eq_empty_iff_forall_notMem.2 fun _ ⟨_, _, _, _, _, _, _, _, _, _, _, hd, _⟩ =>
    (Silmaril.Games.DStrategy.ofHandler_div (maskH I.length)).subset hd

/-- **Divergence of a multi-node component under trap propagation.** When the
first node propagates traps, its environment has only the node's own
divergences (`firstObs`), and the later nodes add, by the fold `nodesObs`, their
own divergences and their chatter with the environment so far, routed through
the node layers above. The outer handlers add nothing. -/
theorem div_denD_multi (C : DCoreSem M) (I : Iface) (nd : Node M) (ns : List (Node M))
    (xs : List Export) (hN : TrapPropagating (Node.denD C I.length nd)) :
    ((Comp.mk I (nd :: ns) xs).denD C).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH I.length) ∧
        t ∈ Strategy.ofHandler (narrowH xs.length) ∧ ∃ d x, Zip d x v ∧
          d ∈ (nodesObs C (I.length + nd.width) ns
            (firstObs I.length (Node.denD C I.length nd))).div ∧
          x ∈ Strategy.ofHandler (exportsH (envAfter I.length (nd :: ns)) xs)} := by
  rw [div_denD_eq, div_denUD, denNodesD_cons, div_denNodesD, obs_ext_maskH _ hN]
  rfl

/-- `div_denD_multi` with every node's strategy propagating traps, at every offset. -/
theorem div_denD_multi_of_forall (C : DCoreSem M) (I : Iface) (nd : Node M)
    (ns : List (Node M)) (xs : List Export)
    (hN : ∀ n ∈ nd :: ns, ∀ e, TrapPropagating (Node.denD C e n)) :
    ((Comp.mk I (nd :: ns) xs).denD C).div = {p | ∃ s t u v, Zip u v s ∧ Zip s t p ∧
      u ∈ Strategy.ofHandler (widenH I.length) ∧
        t ∈ Strategy.ofHandler (narrowH xs.length) ∧ ∃ d x, Zip d x v ∧
          d ∈ (nodesObs C (I.length + nd.width) ns
            (firstObs I.length (Node.denD C I.length nd))).div ∧
          x ∈ Strategy.ofHandler (exportsH (envAfter I.length (nd :: ns)) xs)} :=
  div_denD_multi C I nd ns xs (hN nd List.mem_cons_self I.length)

/-- **Infinite plays of a component with any number of nodes**: a run of the
fold `nodesObs` from `maskH` interleaved with a run of `exportsH`, seen through
`widenH` below and `narrowH` above. -/
theorem inf_denD_nodes (C : DCoreSem M) (I : Iface) (ns : List (Node M)) (xs : List Export) :
    ((Comp.mk I ns xs).denD C).inf = {J | ∃ K, (∃ L, (IsInfPlay L ∧ ∃ R Q,
      (nodesObs C I.length ns (DObs.of (DStrategy.ofHandler (maskH I.length)))).IsRun R ∧
      IsRun (DStrategy.ofHandler (exportsH (envAfter I.length ns) xs)) Q ∧ Interleaved R Q L) ∧
        ThroughBelow (widenH I.length) L K) ∧ ThroughAbove (narrowH xs.length) K J} := by
  rw [Comp.denD, DStrategy.inf_atSizes_iff, Comp.denUD, inf_comp_eq, ← obs_denNodesD]
  rfl

end Silmaril.Wasm.Component
