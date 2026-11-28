module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Constructor.Thms

/-! # Exact finite Unit coproducts and their three-phase payloads -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ
local notation "U" => UnitThreeCycle.One (τ := τ) (Φ := Φ)
local notation "H" => UnitThreeCycle.Three (τ := τ) (Φ := Φ)
local notation "Z" => ofType (Φ := Φ) (Silmaril.empty : τ)

/-- The exact bracketing of a finite coproduct of Unit, including empty
subtrees. -/
inductive UnitTree where
  | empty
  | unit
  | sum (left right : UnitTree)

/-- Interpret this very tree in the syntax type algebra. -/
def UnitTree.ty : UnitTree → τ
  | .empty => Silmaril.empty
  | .unit => Silmaril.unit
  | .sum l r => Silmaril.coprod l.ty r.ty

/-- Interpret the same tree with the native chosen coproduct at each node. -/
noncomputable def UnitTree.obj : UnitTree → P
  | .empty => Z
  | .unit => U
  | .sum l r => l.obj ⨿ r.obj

/-- Replace each Unit leaf by its exact three-Unit phase type. -/
noncomputable def UnitTree.phaseObj : UnitTree → P
  | .empty => Z
  | .unit => H
  | .sum l r => l.phaseObj ⨿ r.phaseObj

/-- Read the chosen coproduct tree at the exact syntax boundary. -/
noncomputable def UnitTree.syntaxIso : (t : UnitTree) → ofType (Φ := Φ) (t.ty : τ) ≅ t.obj
  | .empty => Iso.refl _
  | .unit => Iso.refl _
  | .sum l r => sumIso l.ty r.ty ≪≫ coprod.mapIso l.syntaxIso r.syntaxIso

/-- Keep each tag and replace its Unit payload by literal Unit. -/
noncomputable def UnitTree.reset : (t : UnitTree) → t.obj (τ := τ) (Φ := Φ) ⟶ t.obj
  | .empty => 𝟙 Z
  | .unit => UnitThreeCycle.reset
  | .sum l r => coprod.map l.reset r.reset

/-- Erase only the phase within each leaf of the grouped state. -/
noncomputable def UnitTree.forget : (t : UnitTree) → t.phaseObj (τ := τ) (Φ := Φ) ⟶ t.obj
  | .empty => 𝟙 Z
  | .unit => UnitThreeCycle.forget
  | .sum l r => coprod.map l.forget r.forget

/-- The native representative used for a round on this tree. Both state
boundaries reset only the Unit payloads, and outward exits are forwarded. -/
noncomputable def UnitTree.normalize (t : UnitTree) {B : P} (g : t.obj ⟶ B ⨿ t.obj) :
    t.obj ⟶ B ⨿ t.obj :=
  t.reset ≫ g ≫ coprod.map (𝟙 B) t.reset

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling
