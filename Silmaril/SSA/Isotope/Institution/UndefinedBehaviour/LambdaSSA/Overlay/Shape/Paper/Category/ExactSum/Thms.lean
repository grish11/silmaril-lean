module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.ExactSum.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.ExactSum.Preservation

/-! # The guarded singleton interpretation preserves exact sums and the empty type -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open CategoryTheory CategoryTheory.Limits
open LambdaSSA.Region.Paper.TypeCategory (ofType sumCofan sumCofanIsColimit emptyIsInitial)
open Shape.Category (single sumInl sumInr sumDesc emptyElim)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {A B D : Ty κ}
variable (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))

theorem singleton_map_sumInl (A B : Ty κ) :
    (singletonInterpretation M).map (sumCofan (Φ := Φ) A B).inl = sumInl A B :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum.map_sumInl M A B

theorem singleton_map_sumInr (A B : Ty κ) :
    (singletonInterpretation M).map (sumCofan (Φ := Φ) A B).inr = sumInr A B :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum.map_sumInr M A B

/-- The installed exact sum's copair runs the interpreted selected arm. -/
theorem singleton_map_sumDesc (f : ofType (Φ := Φ) A ⟶ ofType D) (g : ofType B ⟶ ofType D) :
    (singletonInterpretation M).map ((sumCofanIsColimit A B).desc (BinaryCofan.mk f g)) =
      sumDesc ((singletonInterpretation M).map f) ((singletonInterpretation M).map g) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum.map_sumDesc M f g

theorem singleton_map_emptyElim (A : Ty κ) :
    (singletonInterpretation M).map ((emptyIsInitial (Φ := Φ) (τ := Ty κ)).to (ofType A)) = emptyElim (single A) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum.map_emptyElim M A

/-- The image of the installed exact sum is colimiting in the shaped target. -/
noncomputable def singleton_map_sumCofan_isColimit (A B : Ty κ) :
    IsColimit ((singletonInterpretation M).mapCocone (sumCofan (Φ := Φ) A B)) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum.map_sumCofan_isColimit M A B

theorem singleton_preservesFiniteCoproducts :
    PreservesFiniteCoproducts (singletonInterpretation M) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.ExactSum.preservesFinite M

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
