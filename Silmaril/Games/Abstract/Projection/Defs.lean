module

public import Silmaril.Games.Abstract.Module.Defs

/-!
# Projections to abstract functions and modules, and their laws

A projection reads a concrete object (code, a function address under a
semantics, an open module) as an abstract function or a closed abstract
module. The laws relate a relation `R` on the concrete side to an equivalence
on the abstract side. They are separate, because they are separate facts:

* `PreservesFun R κ`: `R`-related objects project to `κ`-equivalent
  functions;
* `ReflectsFun R κ`: `κ`-equivalent projections come from `R`-related
  objects;
* `PreservesMod R` / `ReflectsMod R`: the same for modules, with trap ≈
  divergence equivalence of closed modules.

A projection that both preserves and reflects `R` is an embedding of the
`R`-quotient into the `κ`-quotient. That is a theorem about specific `R`
and `κ`, not the trivial fact that the kernel of a map injects. Each instance
proves its own laws (`Silmaril.Games.Abstract.Projection.Thms`,
`Silmaril.Wasm.Abstract.Projection`).

The projection is a field of the class, and the target types are `outParam`s,
so each concrete type has one projection: no instance ambiguity.
-/

@[expose] public section

namespace Silmaril.Games.Abstract

open Silmaril.Games

universe u v

/-- Concrete objects of type `X` read as abstract functions. -/
class FunProj (X : Type v) (E : outParam Sig.{u}) (S A B : outParam (Type u)) where
  /-- The abstract function of an object. -/
  proj : X → AFun E S A B

/-- Concrete objects of type `X` read as closed abstract modules of shape `sh`. -/
class ModProj (X : Type v) (sh : outParam Shape.{u}) where
  /-- The closed module of an object. -/
  proj : X → sh.ClosedMod

variable {X : Type v}

/-- `R`-related objects project to `κ`-equivalent functions. -/
def PreservesFun {E : Sig.{u}} {S A B O : Type u} [FunProj X E S A B] (R : X → X → Prop)
    (κ : CallBeh E S B → O) : Prop :=
  ∀ x y, R x y → AFun.ObsEquiv κ (FunProj.proj x) (FunProj.proj y)

/-- `κ`-equivalent projections come from `R`-related objects. -/
def ReflectsFun {E : Sig.{u}} {S A B O : Type u} [FunProj X E S A B] (R : X → X → Prop)
    (κ : CallBeh E S B → O) : Prop :=
  ∀ x y, AFun.ObsEquiv κ (FunProj.proj x) (FunProj.proj y) → R x y

/-- `R`-related objects project to trap ≈ divergence equivalent modules. -/
def PreservesMod {sh : Shape.{u}} [ModProj X sh] (R : X → X → Prop) : Prop :=
  ∀ x y, R x y → Shape.ClosedCollapseEquiv (ModProj.proj x) (ModProj.proj y)

/-- Trap ≈ divergence equivalent module projections come from `R`-related
objects. -/
def ReflectsMod {sh : Shape.{u}} [ModProj X sh] (R : X → X → Prop) : Prop :=
  ∀ x y, Shape.ClosedCollapseEquiv (ModProj.proj x) (ModProj.proj y) → R x y

/-- Open modules of a shape, closed by `close`. A wrapper type, so that the
projection is an instance of its own. -/
structure OpenModule (sh : Shape.{u}) : Type u where
  /-- The open module. -/
  mod : sh.OpenMod

instance (sh : Shape.{u}) : ModProj (OpenModule sh) sh := ⟨fun m => Shape.close m.mod⟩

end Silmaril.Games.Abstract
