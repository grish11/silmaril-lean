module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Independence.Thms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringModelBoundary

/-! # The Conway matrix separator fails constructor-map uniformity -/

public section

universe u v

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

open CategoryTheory CategoryTheory.Limits Guardedness

/-- For graph matrices, the typed constructor returning Unit on either input
tag violates uniformity. The same weighted square supplies the failure. -/
theorem not_uniform_unit_constructor :
    ¬ conway.toFixpoints.UniformAt
      (relabel (X := coproducts.sum one one) (Y := one) (fun _ => ())) :=
  Proofs.CounterSemiringModelBoundary.not_uniform_unit_constructor

/-- The failure holds for any coordinate choices for a coproduct of two
copies of the one-state object. -/
theorem not_uniform_coproduct_fold {X Z : Object.{0}} (u : one ≅ X) (l r : X ⟶ Z)
    (colim : IsColimit (BinaryCofan.mk l r)) (h : Z ⟶ X)
    (hl : l ≫ h = 𝟙 X) (hr : r ≫ h = 𝟙 X) : ¬ conway.toFixpoints.UniformAt h :=
  Proofs.CounterSemiringModelBoundary.not_uniform_coproduct_fold u l r colim h hl hr

/-- Any coproduct-preserving value embedding with the one-state object in its
essential image carries a pure fold on which matrix iteration is nonuniform.
The obstruction uses the value/computation coproduct comparison alone. -/
theorem not_uniform_value_fold {V : Type u} [Category.{v} V] [HasBinaryCoproducts V]
    (J : V ⥤ Object.{0}) [PreservesColimitsOfShape (Discrete WalkingPair) J]
    (X : V) (u : one ≅ J.obj X) :
    ¬ conway.toFixpoints.UniformAt (J.map (coprod.desc (𝟙 X) (𝟙 X))) :=
  Proofs.CounterSemiringModelBoundary.not_uniform_value_fold J X u

/-- The Unit constructor is the terminal value map on the coproduct input.
Consequently the obstruction applies to any compatible interpretation of
that constructor whose Unit object is isomorphic to the one-state carrier. -/
theorem not_uniform_value_unit_discard {V : Type u} [Category.{v} V] [HasBinaryCoproducts V]
    (J : V ⥤ Object.{0}) [PreservesColimitsOfShape (Discrete WalkingPair) J]
    (U : V) (terminal : IsTerminal U) (u : one ≅ J.obj U) :
    ¬ conway.toFixpoints.UniformAt (J.map (terminal.from (U ⨿ U))) := by
  rw [terminal.hom_ext (terminal.from (U ⨿ U)) (coprod.desc (𝟙 U) (𝟙 U))]
  exact not_uniform_value_fold J U u

/-- Thus a coproduct-preserving value functor containing the one-state
carrier cannot supply the uniformity field for these matrix iterates. -/
theorem not_uniform_value_functor {V : Type u} [Category.{v} V] [HasBinaryCoproducts V]
    (J : V ⥤ Object.{0}) [PreservesColimitsOfShape (Discrete WalkingPair) J]
    (X : V) (u : one ≅ J.obj X) : ¬ conway.toFixpoints.Uniform J := by
  intro uniform
  exact not_uniform_value_fold J X u (fun f g hf hg square =>
    uniform f g (coprod.desc (𝟙 X) (𝟙 X)) hf hg square)

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix
