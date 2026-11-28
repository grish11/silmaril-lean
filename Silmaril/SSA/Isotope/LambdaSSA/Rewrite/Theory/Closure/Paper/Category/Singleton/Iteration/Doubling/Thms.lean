module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NativeDoubling

/-! # Standard Paper doubling with reset-invariant recursive outputs -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

/-- Iterating two consecutive steps gives the original iteration if an
idempotent reset leaves recursive outputs unchanged and has the same native
constructor realization on both tagged copies. The first step may observe
its input, execute effects, and exit. -/
theorem iterate_double_of_output_reset {D T B : P} (split : D ⨿ D ≅ T)
    (forget : T ⟶ D) (hForget : ConstructorReturn forget) (reset : D ⟶ D)
    (hl : (coprod.inl ≫ split.hom) ≫ forget = reset)
    (hr : (coprod.inr ≫ split.hom) ≫ forget = reset)
    (idem : reset ≫ reset = reset) (g : D ⟶ B ⨿ D) (output : g ≫ coprod.map (𝟙 B) reset = g) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NativeDoubling.of_output_reset
    split forget hForget reset hl hr idem g output

local notation "U" => ofType (Φ := Φ) (Silmaril.unit : τ)

/-- For a step that already returns the Unit constructor on recurrence, the
reset is literal constructor discard. This uses standard Paper's equations. -/
theorem iterate_double_of_unit_reset {B : P} (g : U ⟶ B ⨿ U)
    (output : g ≫ coprod.map (𝟙 B) (discardArrow (Φ := Φ) (Silmaril.unit : τ)) = g) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.NativeDoubling.of_unit_output_reset g output

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
