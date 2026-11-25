module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Suspension.Defs
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] (P : Coproducts C)
  (T : CategoryTheory.Monad C) (H : C ⥤ C)
  (R : FinalResumptions (parametrized P T H))

theorem resumption_map_outFor {X Y : C} (f : X ⟶ Y) :
    (R.monad P).map f ≫ R.out Y =
      R.out X ≫ T.map (P.map f (H.map ((R.monad P).map f))) := by
  let k : R.obj X ⟶ R.obj Y := (R.monad P).map f
  rw [map_outOf R P f]
  change R.out X ≫ T.map (P.map (𝟙 X) (H.map k)) ≫
    ((family P T).obj (H.obj (R.obj Y))).map f = R.out X ≫ T.map (P.map f (H.map k))
  rw [family_map, ← Functor.map_comp]
  have e : P.map (𝟙 X) (H.map k) ≫ P.map f (𝟙 (H.obj (R.obj Y))) = P.map f (H.map k) := by
    apply P.hom_ext <;> simp [Coproducts.map]
  rw [e]

@[reassoc]
theorem step_outFor (X : C) :
    liftStepFor P T H R X ≫ R.out X = H.map (R.unit X) ≫ raise P T (H.obj (R.obj X)) X := by
  unfold liftStepFor
  rw [Category.assoc, Category.assoc, R.roll_out]
  exact congrArg (H.map (R.unit X) ≫ ·) (Category.comp_id _)

theorem step_natFor {X Y : C} (f : X ⟶ Y) :
    H.map f ≫ liftStepFor P T H R Y = liftStepFor P T H R X ≫ (R.monad P).map f := by
  let k : R.obj X ⟶ R.obj Y := (R.monad P).map f
  have e : R.unit X ≫ k = f ≫ R.unit Y := by
    change (R.monad P).η.app X ≫ (R.monad P).map f = f ≫ (R.monad P).η.app Y
    exact (R.monad P).η.naturality f |>.symm
  have er : raise P T (H.obj (R.obj X)) X ≫ T.map (P.map f (H.map k)) =
      H.map k ≫ raise P T (H.obj (R.obj Y)) Y := by
    change raise P T (H.obj (R.obj X)) X ≫ T.map (P.map f (H.map k)) =
      H.map k ≫ P.inr ≫ T.η.app (P.sum Y (H.obj (R.obj Y)))
    simp only [raise, Category.assoc, ← T.η.naturality, Coproducts.map, Functor.id_map,
      Coproducts.inr_desc_assoc]
  have h : (H.map f ≫ liftStepFor P T H R Y) ≫ R.out Y =
      (liftStepFor P T H R X ≫ k) ≫ R.out Y := by
    rw [Category.assoc, step_outFor, Category.assoc, show k ≫ R.out Y = _ from resumption_map_outFor P T H R f]
    conv_rhs => rw [← Category.assoc, step_outFor]
    rw [Category.assoc, er]
    exact (H.map_comp_assoc f (R.unit Y) _).symm.trans
      ((congrArg (fun p => H.map p ≫ raise P T (H.obj (R.obj Y)) Y) e.symm).trans
        (H.map_comp_assoc (R.unit X) k _))
  change _ = liftStepFor P T H R X ≫ k
  simpa only [Category.assoc, R.out_roll, Category.comp_id] using congrArg (· ≫ R.roll Y) h

theorem suspension_guardFor [HasInitial C] (G : MonadGuardedness P T) :
    MonadGuardedness.GuardedNatTrans P ((parametrizedGuards G H).resumptionGuardedness R)
      ({ app := liftStepFor P T H R, naturality := fun _ _ f => step_natFor P T H R f } :
        H ⟶ ((R.monad P : CategoryTheory.Monad C) : C ⥤ C)) := by
  intro Y
  let A := P.sum (⊥_ C) Y
  let E := H.obj (R.obj A)
  let j : Y ⟶ A := P.inr
  let g : H.obj Y ⟶ T.obj (P.sum (⊥_ C) E) :=
    H.map j ≫ H.map (R.unit A) ≫ raise P T E (⊥_ C)
  change G.guarded (Y := Kleisli.mk T (P.sum (⊥_ C) E)) (Z := Kleisli.mk T Y)
    (kleisliArrow (((liftStepFor P T H R Y ≫ (R.monad P).map j) ≫ R.out A) ≫ T.map (rearrange P E)))
  have q : ((liftStepFor P T H R Y ≫ (R.monad P).map j) ≫ R.out A) ≫ T.map (rearrange P E) =
      g ≫ T.map (P.inl (X := P.sum (⊥_ C) E) (Y := Y)) := by
    rw [← step_natFor P T H R j, Category.assoc, Category.assoc, step_outFor_assoc]
    have e : raise P T E A ≫ T.map (rearrange P E (Y := ⊥_ C) (Z := Y)) =
        raise P T E (⊥_ C) ≫ T.map (P.inl (Y := Y)) := by
      simp [raise, A, Category.assoc, ← T.η.naturality, rearrange]
    change H.map j ≫ H.map (R.unit A) ≫ raise P T E A ≫ T.map (rearrange P E) =
      g ≫ T.map (P.inl (Y := Y))
    simp only [g, Category.assoc, e]
  rw [q]
  exact Eq.mp (congrArg (G.guarded (Y := Kleisli.mk T (P.sum (⊥_ C) E))
    (Z := Kleisli.mk T Y)) (Kleisli.hom_ext (comp_pure_of T (kleisliArrow g) P.inl)))
    (G.trivial (kleisliArrow g))

end Silmaril.Calco2019.Proofs
