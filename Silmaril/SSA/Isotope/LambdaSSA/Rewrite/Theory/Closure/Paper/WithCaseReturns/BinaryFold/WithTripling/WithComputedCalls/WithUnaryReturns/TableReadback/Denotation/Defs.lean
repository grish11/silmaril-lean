module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Live.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Dispatcher.Defs

/-! # Iteration transport used by captured table packing -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [HasFiniteCoproducts C] [Iteration C]

/-- The feedback comparison for an invertible value change of coordinates.
The exit object and its injection are fixed. -/
def PureIsoIteration (J : V ⥤ C) : Prop :=
  ∀ {A P B : V} (p : A ≅ P)
    (f : J.obj A ⟶ J.obj B ⨿ J.obj A) (g : J.obj P ⟶ J.obj B ⨿ J.obj P),
    f ≫ coprod.map (𝟙 _) (J.map p.hom) = J.map p.hom ≫ g →
    iterate f = J.map p.hom ≫ iterate g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
