module

public import Silmaril.Wasm.Component.DWiringMono.Defs
public import Silmaril.Wasm.Component.DWiring.Thms
public import Silmaril.Games.DivComp.Thms
public import Silmaril.Games.DPair.Thms
import Silmaril.Proofs.Wasm.Component.DWiringMono.Basic

/-!
# Monotonicity and congruence of the divergence-observing denotation

The divergence-observing component denotation of `Silmaril.Wasm.Component.DWiring` is the
divergence-aware lift of `Comp.denU`, built from the same wiring with `DStrategy.comp`,
`DStrategy.pair` and `DStrategy.ofHandler`. Like `Comp.denU` (`Component.denU_mono`), it is
monotone in the core semantics, for the refinement order of `DStrategy` (finite plays,
divergences and infinite plays):

* `ext_mono`, `dcoreNode_mono`;
* `denUD_mono : C.Le C' → c.denUD C ≤ c.denUD C'` (with `denNodesD_mono`, `node_denD_mono`);
* `denD_mono`, `linked_denUD_mono`, `program_denUD_mono`.

Hence equal core strategies give equal denotations (`denUD_congr`, `denD_congr`).

Proofs are in `Silmaril.Proofs.Wasm.Component.DWiringMono`.
-/

public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

variable {M : Type} [CoreModule M]

namespace DStrategy

/-- Extending an environment is monotone in the environment and the instance. -/
theorem ext_mono {X : Sig.{0}} (e : Nat) {D D' : Games.DStrategy X sigU}
    {N N' : Games.DStrategy sigU sigU} (hD : D ≤ D') (hN : N ≤ N') : ext e D N ≤ ext e D' N' :=
  Silmaril.Proofs.Wasm.Component.DWiringMono.ext_mono e hD hN

/-- `atSizes` is monotone. -/
theorem atSizes_mono (n k : Nat) {σ σ' : Games.DStrategy sigU sigU} (h : σ ≤ σ') :
    atSizes n k σ ≤ atSizes n k σ' :=
  Games.DStrategy.comp_mono (Games.DStrategy.comp_mono le_rfl h) le_rfl

end DStrategy

theorem dcoreNode_mono {C C' : DCoreSem M} (h : C.Le C') (e : Nat) (m : M) (args : List Impl) :
    dcoreNode C e m args ≤ dcoreNode C' e m args :=
  Silmaril.Proofs.Wasm.Component.DWiringMono.dcoreNode_mono h e m args

/-- **Refining the core semantics refines every component**, divergences and infinite plays
included. -/
theorem denUD_mono {C C' : DCoreSem M} (h : C.Le C') (c : Comp M) : c.denUD C ≤ c.denUD C' :=
  Silmaril.Proofs.Wasm.Component.DWiringMono.denUD_mono h c

theorem denNodesD_mono {C C' : DCoreSem M} (h : C.Le C') {X : Sig.{0}} (e : Nat)
    (ns : List (Node M)) {D D' : Games.DStrategy X sigU} (hD : D ≤ D') :
    denNodesD C e ns D ≤ denNodesD C' e ns D' :=
  Silmaril.Proofs.Wasm.Component.DWiringMono.denNodesD_mono h e ns hD

theorem node_denD_mono {C C' : DCoreSem M} (h : C.Le C') (e : Nat) (n : Node M) :
    Node.denD C e n ≤ Node.denD C' e n :=
  Silmaril.Proofs.Wasm.Component.DWiringMono.node_denD_mono h e n

/-- Refining the core semantics refines every component at its interface signatures. -/
theorem denD_mono {C C' : DCoreSem M} (h : C.Le C') (c : Comp M) : c.denD C ≤ c.denD C' :=
  DStrategy.atSizes_mono _ _ (denUD_mono h c)

theorem linked_denUD_mono {C C' : DCoreSem M} (h : C.Le C') (l : Linked M) :
    l.denUD C ≤ l.denUD C' :=
  Games.DStrategy.comp_mono
    (Silmaril.Proofs.Wasm.Component.DWiringMono.linked_go_mono h _ _ le_rfl) le_rfl

theorem program_denUD_mono {C C' : DCoreSem M} (h : C.Le C') (p : Program M) :
    p.denUD C ≤ p.denUD C' :=
  Silmaril.Proofs.Wasm.Component.DWiringMono.program_denUD_mono h p

/-- **Equal core strategies give equal divergence-aware denotations.** -/
theorem denUD_congr {C C' : DCoreSem M} (h : ∀ m, C.sem m = C'.sem m) (c : Comp M) :
    c.denUD C = c.denUD C' :=
  le_antisymm (denUD_mono (fun m => (h m).le) c) (denUD_mono (fun m => (h m).ge) c)

theorem denD_congr {C C' : DCoreSem M} (h : ∀ m, C.sem m = C'.sem m) (c : Comp M) :
    c.denD C = c.denD C' :=
  congrArg (DStrategy.atSizes _ _) (denUD_congr h c)

end Silmaril.Wasm.Component
