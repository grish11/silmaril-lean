module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Trees of native constructor state maps -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

/-- Uniformity for a specified native arrow and all its typed local squares. -/
def UniformStateMap {A D : P} (h : A ⟶ D) : Prop :=
  ∀ {B : P} (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D),
    f ≫ coprod.map (𝟙 B) h = h ≫ g → iterate f = h ≫ iterate g

/-- The actual coproduct tree of a map with a native constructor return at
each leaf. The source and target trees have matching branch positions. -/
inductive ConstructorCoproduct : {A D : P} → (A ⟶ D) → Prop where
  | leaf {A D : P} {h : A ⟶ D} : ConstructorReturn h → ConstructorCoproduct h
  | sum {A C D E : P} {h : A ⟶ C} {k : D ⟶ E} :
      ConstructorCoproduct h → ConstructorCoproduct k → ConstructorCoproduct (coprod.map h k)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
