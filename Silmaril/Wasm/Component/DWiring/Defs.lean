module

public import Silmaril.Wasm.Component.Semantics.Defs
public import Silmaril.Games.DivComp.Defs
public import Silmaril.Games.DivLTS.Defs
public import Silmaril.Games.DPair.Defs

/-!
# Divergence-observing wiring and component denotation

The wiring operations of `Silmaril.Wasm.Component.Wiring` and the component
denotation `Comp.denU` of `Silmaril.Wasm.Component.Semantics`, rebuilt over
divergence-observing strategies (`Silmaril.Games.DStrategy`). Every definition
has exactly the shape of its ordinary counterpart, with `DStrategy.comp`,
`DStrategy.ofHandler`, `DStrategy.pair` and `DStrategy.id` in place of the
`Strategy` versions:

* `DStrategy.atSizes n k σ`: `σ` between `widenH n` (below) and `narrowH k`
  (on top), as `atSizes`;
* `DStrategy.ext e D N`: `D.comp (((DStrategy.id sigU).pair N).comp
  (ofHandler (splitH e)))`, as `ext`;
* `DCoreSem`: a divergence-observing strategy for each core module;
  `DCoreSem.forget` its finite plays, a `CoreSem`;
* `dcoreNode`, `Comp.denD`/`Comp.denUD`/`denNodesD`/`Node.denD`,
  `Linked.denUD`, `Program.denUD`: the denotations.

`Silmaril.Wasm.Component.DWiring.Thms` shows that forgetting divergence and
infinite plays gives back the ordinary operations (`toStrategy_atSizes`, …,
`toStrategy_denD : (c.denD C).toStrategy = c.den C.forget`) and computes the
divergences and infinite plays of `atSizes`.
-/

@[expose] public section

namespace Silmaril.Wasm.Component

open Silmaril.Games

namespace DStrategy

/-- A divergence-observing strategy over `sigU` seen at the interface sizes `n`
(imports) and `k` (exports); see `atSizes`. -/
def atSizes (n k : Nat) (σ : DStrategy sigU sigU) : DStrategy (sigN n) (sigN k) :=
  ((DStrategy.ofHandler (widenH n)).comp σ).comp (DStrategy.ofHandler (narrowH k))

/-- Extend the environment `D` (of `e` functions) by an instance `N`; see `ext`. -/
def ext {X : Sig.{0}} (e : Nat) (D : DStrategy X sigU) (N : DStrategy sigU sigU) :
    DStrategy X sigU :=
  D.comp (((DStrategy.id sigU).pair N).comp (DStrategy.ofHandler (splitH e)))

end DStrategy

variable {M : Type} [CoreModule M]

/-- A divergence-observing semantics of core modules. -/
structure DCoreSem (M : Type) [CoreModule M] where
  /-- The divergence-observing strategy of a core module. -/
  sem : (m : M) → DStrategy (CoreIface.sig (CoreModule.imports m))
    (CoreIface.sig (CoreModule.exports m))

/-- The finite plays of a divergence-observing core semantics. -/
def DCoreSem.forget (C : DCoreSem M) : CoreSem M := ⟨fun m => (C.sem m).toStrategy⟩

/-- A core instance of `m` with the wiring `args`; see `coreNode`. -/
def dcoreNode (C : DCoreSem M) (e : Nat) (m : M) (args : List Impl) : DStrategy sigU sigU :=
  (DStrategy.ofHandler (implsN e args (CoreModule.imports m).length)).comp
    ((C.sem m).comp (DStrategy.ofHandler (widenH (CoreModule.exports m).length)))

mutual
/-- The divergence-observing strategy of a component, over `sigU`; see
`Comp.denU`. -/
def Comp.denUD (C : DCoreSem M) : Comp M → DStrategy sigU sigU
  | .mk I ns xs =>
    (denNodesD C I.length ns (DStrategy.ofHandler (maskH I.length))).comp
      (DStrategy.ofHandler (exportsH (envAfter I.length ns) xs))

/-- Extend the environment `D` (of `e` functions) by the nodes `ns`; see
`denNodes`. -/
def denNodesD (C : DCoreSem M) {X : Sig.{0}} : Nat → List (Node M) → DStrategy X sigU →
    DStrategy X sigU
  | _, [], D => D
  | e, n :: ns, D => denNodesD C (e + n.width) ns (DStrategy.ext e D (Node.denD C e n))

/-- The divergence-observing strategy of a node; see `Node.den`. -/
def Node.denD (C : DCoreSem M) : Nat → Node M → DStrategy sigU sigU
  | e, .core m args => dcoreNode C e m args
  | e, .inst c args => (DStrategy.ofHandler (implsH e args)).comp (Comp.denUD C c)
end

/-- **The divergence-observing strategy of a component**, at its interface
signatures; see `Comp.den`. -/
def Comp.denD (C : DCoreSem M) (c : Comp M) :
    DStrategy c.imports.sig (sigN c.exports.length) :=
  DStrategy.atSizes _ _ (c.denUD C)

/-- The divergence-observing strategy of a flat component, over `sigU`; see
`Linked.denU`. -/
def Linked.denUD (C : DCoreSem M) (l : Linked M) : DStrategy sigU sigU :=
  (go l.imports.length l.nodes (DStrategy.ofHandler (maskH l.imports.length))).comp
    (DStrategy.ofHandler (exportsH (linkedEnv l.imports.length l.nodes) l.exports))
where
  /-- Extend the environment by core instances. -/
  go {X : Sig.{0}} : Nat → List (M × List Impl) → DStrategy X sigU → DStrategy X sigU
    | _, [], D => D
    | e, n :: ns, D =>
      go (e + (CoreModule.exports n.1).length) ns (DStrategy.ext e D (dcoreNode C e n.1 n.2))

/-- The divergence-observing strategy of a program; see `Program.denU`. -/
def Program.denUD (C : DCoreSem M) (p : Program M) : DStrategy sigU sigU :=
  match p.observe with
  | none => p.comp.denUD C
  | some obs => (p.comp.denUD C).comp (DStrategy.ofHandler (selectH obs))

end Silmaril.Wasm.Component
