module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Defs
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Suspension.Thms
import Silmaril.Proofs.Semantics.Calco2019.ExceptionResumption

/-! # Guardedness and preservation for the embeddings of Lemma 27 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (H : C ⥤ C)
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

/-- A map of result types acts on both the return and the suspended continuation. -/
@[reassoc]
theorem resumption_map_out {X Y : C} (f : X ⟶ Y) :
    (R.monad P).map f ≫ R.out Y =
      R.out X ≫ T.monad.map (P.map f (H.map ((R.monad P).map f))) :=
  Proofs.resumption_map_out T H R f

@[reassoc, simp]
theorem liftBase_out (X : C) :
    liftBase T H R X ≫ R.out X = T.monad.map (P.inl (Y := H.obj (R.obj X))) :=
  Proofs.base_out T H R X

@[reassoc, simp]
theorem liftStep_out (X : C) :
    liftStep T H R X ≫ R.out X = H.map (R.unit X) ≫ raise P T.monad (H.obj (R.obj X)) X :=
  liftStepFor_out P T.monad H R X

/-- The suspension generator of Lemma 27(1). -/
noncomputable def suspension : H ⟶ ((R.monad P : CategoryTheory.Monad C) : C ⥤ C) :=
  suspensionFor P T.monad H R

@[simp]
theorem suspension_app (X : C) : (suspension T H R).app X = liftStep T H R X :=
  suspensionFor_app P T.monad H R X

/-- Every suspension is guarded in its entire output. -/
theorem suspension_guarded [HasInitial C] :
    MonadGuardedness.GuardedNatTrans P ((parametrizedElgot T H).resumptionElgotMonad R).guard
      (suspension T H R) :=
  suspensionFor_guarded P T.monad H R T.guard

/-- The embedding of the base monad preserves unit and bind. -/
noncomputable def baseMonadHom : T.monad ⟶ R.monad P where
  app := liftBase T H R
  naturality _ _ f := Proofs.base_nat T H R f
  app_η := Proofs.base_unit T H R
  app_μ := Proofs.base_mul T H R

/-- The embedding of Lemma 27(2) preserves guards and chosen iteration. -/
noncomputable def baseEmbedding :
    GuardedElgotMonadHom P T ((parametrizedElgot T H).resumptionElgotMonad R) where
  hom := baseMonadHom T H R
  guarded f hf := ((parametrizedElgot T H).resumptionGuardedness_iff R _).mpr
    (Proofs.base_guard T H R f hf)
  iteration f hf := Proofs.base_iteration T H R f hf

@[simp]
theorem baseEmbedding_app (X : C) : (baseEmbedding T H R).hom.app X = liftBase T H R X :=
  by unfold baseEmbedding baseMonadHom; rfl

end Silmaril.Calco2019.Exception
