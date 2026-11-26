module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle

/-! # Tripling Unit-state feedback using native constructor uniformity -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.UnitThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ
local notation "U" => One (τ := τ) (Φ := Φ)

/-- In the chosen three-phase coordinates, each phase forgets to a literal Unit. -/
theorem phase_discards :
    (coprod.inl ≫ (split (τ := τ) (Φ := Φ)).inv ≫ forget = reset) ∧
    (coprod.inl ≫ coprod.inr ≫ (split (τ := τ) (Φ := Φ)).inv ≫ forget = reset) ∧
    (coprod.inr ≫ coprod.inr ≫ (split (τ := τ) (Φ := Φ)).inv ≫ forget = reset) :=
  ⟨by simpa only [Category.assoc] using
      Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle.zero_forget (τ := τ) (Φ := Φ),
   by simpa only [Category.assoc] using
      Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle.one_forget (τ := τ) (Φ := Φ),
   by simpa only [Category.assoc] using
      Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle.two_forget (τ := τ) (Φ := Φ)⟩

/-- Discarding the native cycle tags commutes with a round that absorbs
literal Unit on input and on recurrence. -/
theorem native_square {B : P} (g : U ⟶ B ⨿ U)
    (input : reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    step g ≫ coprod.map (𝟙 B) forget = forget ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle.native_square g input output

/-- The native constructor simulation identifies the two feedback arrows. -/
theorem native_iterate {B : P} (g : U ⟶ B ⨿ U)
    (input : reset ≫ g = g) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    iterate (step g) = forget ≫ iterate g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle.native_iterate g input output

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.UnitThreeCycle

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "U" => ofType Seed (Silmaril.unit : τ)

/-- Project the native discard square for this very round and eliminate its
three phases. The result compares one round with three at the same type. -/
theorem triple_step_of_native_reset
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {B : Paper.TypeCategory (τ := τ) Φ}
    (g : Paper.TypeCategory.UnitThreeCycle.One ⟶ B ⨿ Paper.TypeCategory.UnitThreeCycle.One)
    (input : Paper.TypeCategory.UnitThreeCycle.reset ≫ g = g)
    (output : g ≫ coprod.map (𝟙 B) Paper.TypeCategory.UnitThreeCycle.reset = g) :
    iterateChosen Seed (triple (projectStep Seed g)) = iterateChosen Seed (projectStep Seed g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle.triple_step_of_native_reset
    Seed includeUnit g input output

/-- Unit η transfers the native discard square to every Unit-state step in
the quotient, including effectful steps and arbitrary exit types. -/
theorem triple_step_unit
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {B : TypeCategory Seed} (g : U ⟶ B ⨿ U) :
    iterateChosen Seed (triple g) = iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitThreeCycle.triple_step Seed includeUnit g

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
