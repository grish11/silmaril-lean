module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Defs

/-! # Finite structural recurrence types -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

/-- The exact recurrence type, retaining the original product and sum brackets. -/
inductive StructuralState where
  | empty
  | unit
  | sum (left right : StructuralState)
  | product (left right : StructuralState)

universe u
variable {τ : Type u} [TypeFormers τ]

def StructuralState.ty : StructuralState → τ
  | .empty => Silmaril.empty
  | .unit => Silmaril.unit
  | .sum l r => Silmaril.coprod l.ty r.ty
  | .product l r => Silmaril.product l.ty r.ty

/-- Distribute the left factor over the right tree. -/
def UnitTree.product (l : UnitTree) : UnitTree → UnitTree
  | .empty => .empty
  | .unit => l
  | .sum r s => .sum (l.product r) (l.product s)

/-- Normalize a structural type to a finite coproduct of Unit. -/
def StructuralState.tree : StructuralState → UnitTree
  | .empty => .empty
  | .unit => .unit
  | .sum l r => .sum l.tree r.tree
  | .product l r => l.tree.product r.tree

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed

/-- Change the recursive input and output coordinates, retaining the same exit object. -/
noncomputable abbrev transportStep {A D B : Q} (e : A ≅ D) (g : D ⟶ B ⨿ D) : A ⟶ B ⨿ A :=
  e.hom ≫ g ≫ coprod.map (𝟙 B) e.inv

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
