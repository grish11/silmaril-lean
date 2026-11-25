module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Thms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (H : C ⥤ C)
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

private noncomputable def delayedBody (X : C) : R.obj X ⟶ R.obj (P.sum X (R.obj X)) :=
  let A := P.sum X (R.obj X)
  let j : R.obj X ⟶ R.obj A := P.inr ≫ R.unit A
  R.out X ≫ T.monad.map (P.map (P.inl (Y := R.obj X)) (H.map j)) ≫ R.roll A

private noncomputable def delayedReturn (X : C) :
    R.obj X ⟶ ((parametrizedElgot T H).obj (R.obj (P.sum X (R.obj X)))).monad.obj X :=
  let A := P.sum X (R.obj X)
  let j : R.obj X ⟶ R.obj A := P.inr ≫ R.unit A
  R.out X ≫ T.monad.map (P.map (𝟙 X) (H.map j))

private theorem delayed_observation (X : C) :
    let A := P.sum X (R.obj X)
    let L := ((parametrizedElgot T H).obj (R.obj A)).monad
    (kleisliArrow (delayedBody T H R X ≫ R.out A) :
        Kleisli.mk L (R.obj X) ⟶ Kleisli.mk L A) =
      kleisliArrow (delayedReturn T H R X) ≫ (P.kleisli L).inl (Y := Kleisli.mk L (R.obj X)) := by
  intro A L
  let Q := T.monad
  let j : R.obj X ⟶ R.obj A := P.inr ≫ R.unit A
  have map_eq : L.map (P.inl (X := X) (Y := R.obj X)) =
      Q.map (P.map P.inl (𝟙 (H.obj (R.obj A)))) := family_map P Q _ _
  have e : P.map (𝟙 X) (H.map j) ≫ P.map (P.inl (X := X) (Y := R.obj X))
        (𝟙 (H.obj (R.obj A))) =
      P.map (P.inl (X := X) (Y := R.obj X)) (H.map j) := by
    apply P.hom_ext <;> simp [Coproducts.map, Category.assoc]
  apply Kleisli.hom_ext
  have hp := comp_pure_of L (kleisliArrow (delayedReturn T H R X))
    (P.inl (X := X) (Y := R.obj X))
  change _ = (kleisliArrow (delayedReturn T H R X) ≫
    (Kleisli.Adjunction.toKleisli L).map (P.inl (X := X) (Y := R.obj X))).of
  rw [hp, map_eq]
  change (R.out X ≫ Q.map (P.map P.inl (H.map j)) ≫ R.roll A) ≫ R.out A =
    (R.out X ≫ Q.map (P.map (𝟙 X) (H.map j))) ≫ Q.map (P.map P.inl (𝟙 (H.obj (R.obj A))))
  simp only [Category.assoc, R.roll_out, ← Functor.map_comp, e]
  exact congrArg (R.out X ≫ ·) (Category.comp_id _)

private theorem delayed_guard (X : C) :
    (parametrizedElgot T H).ResumptionGuard R (Y := X) (Z := R.obj X) (delayedBody T H R X) := by
  let A := P.sum X (R.obj X)
  let M := parametrizedElgot T H
  let L := (M.obj (R.obj A)).monad
  change (M.obj (R.obj A)).guard.guarded (Y := Kleisli.mk L X) (Z := Kleisli.mk L (R.obj X))
    (kleisliArrow (delayedBody T H R X ≫ R.out A))
  rw [delayed_observation T H R X]
  exact (M.obj (R.obj A)).guard.trivial _

private theorem delayed_iteration (X : C) :
    (parametrizedElgot T H).iterateResumption R (delayedBody T H R X) (delayed_guard T H R X) =
      𝟙 (R.obj X) := by
  let A := P.sum X (R.obj X)
  let M := parametrizedElgot T H
  let L := (M.obj (R.obj A)).monad
  let K := P.kleisli L
  let x := Kleisli.mk L X
  let r := Kleisli.mk L (R.obj X)
  let b : r ⟶ K.sum x r := kleisliArrow (delayedBody T H R X ≫ R.out A)
  let d : r ⟶ x := kleisliArrow (delayedReturn T H R X)
  let F := (M.obj (R.obj A)).iteration
  let q := F.iterate b (delayed_guard T H R X)
  have eq : b = d ≫ K.inl := delayed_observation T H R X
  have fix : b ≫ K.desc (𝟙 x) q = q := F.fixpoint b (delayed_guard T H R X)
  have q_eq : q = d := by
    rw [eq, Category.assoc, Coproducts.inl_desc, Category.comp_id] at fix
    exact fix.symm
  have diamond : M.diamond R (delayedBody T H R X) (delayed_guard T H R X) =
      delayedReturn T H R X := congrArg Kleisli.Hom.of q_eq
  let j : R.obj X ⟶ R.obj A := P.inr ≫ R.unit A
  let k := R.extend P (P.desc (R.unit X) (𝟙 (R.obj X)))
  have jk : j ≫ k = 𝟙 (R.obj X) := by
    change (P.inr ≫ R.unit A) ≫ R.extend P (P.desc (R.unit X) (𝟙 (R.obj X))) = _
    rw [Category.assoc, R.unit_extend, Coproducts.inr_desc]
  have maps : P.map (𝟙 X) (H.map j) ≫ P.map (𝟙 X) (H.map k) = 𝟙 (P.sum X (H.obj (R.obj X))) := by
    have h : H.map j ≫ H.map k = 𝟙 (H.obj (R.obj X)) := by rw [← H.map_comp, jk, H.map_id]
    apply P.hom_ext
    · simp [Coproducts.map]
    · simp only [Coproducts.map, Category.assoc, Coproducts.inr_desc_assoc, Coproducts.inr_desc,
          Category.id_comp]
      rw [← Category.assoc, h, Category.id_comp]
      exact (Category.comp_id _).symm
  have solution : R.IsSolution P (delayedReturn T H R X) (𝟙 (R.obj X)) := by
    change 𝟙 (R.obj X) ≫ R.out X = (R.out X ≫ T.monad.map (P.map (𝟙 X) (H.map j))) ≫
      T.monad.map (P.map (𝟙 X) (H.map k))
    rw [Category.id_comp, Category.assoc, ← Functor.map_comp, maps, Functor.map_id]
    exact (Category.comp_id _).symm
  change R.solve P (M.diamond R (delayedBody T H R X) (delayed_guard T H R X)) = _
  rw [diamond]
  exact (R.solve_unique P _ _ solution).symm

private theorem liftBase_extend_out {X Y : C} (f : X ⟶ R.obj Y) :
    liftBase T H R X ≫ R.extend P f ≫ R.out Y =
      T.monad.map (f ≫ R.out Y) ≫ T.monad.μ.app (P.sum Y (H.obj (R.obj Y))) := by
  let Q := T.monad
  let k := R.extend P f
  let M := (parametrizedElgot T H).toParametrizedMonad
  let E := H.obj (R.obj Y)
  let A := P.sum Y E
  let b : P.sum X E ⟶ Q.obj A := P.desc (f ≫ R.out Y) (raise P Q E Y)
  have hinl : Q.map (P.inl (X := X) (Y := H.obj (R.obj X))) ≫ (M.parameter X).map k =
      Q.map (P.inl (X := X) (Y := E)) := by
    change Q.map P.inl ≫ Q.map (P.map (𝟙 X) (H.map k)) = _
    rw [← Functor.map_comp]
    simp [Coproducts.map]
  have he : M.extend (W := R.obj Y) (f ≫ R.out Y) = Q.map b ≫ Q.μ.app A :=
    family_extend P Q E (f ≫ R.out Y)
  rw [show k ≫ R.out Y = _ from R.extend_spec P f]
  rw [← Category.assoc, liftBase_out T H R X, ← Category.assoc, hinl, he]
  rw [← Functor.map_comp_assoc, Coproducts.inl_desc]

private theorem delayed_body_generators (X : C) :
    let A := P.sum X (R.obj X)
    let E := H.obj (R.obj X)
    delayedBody T H R X =
      R.out X ≫ liftBase T H R (P.sum X E) ≫
        R.extend P (P.desc (P.inl ≫ R.unit A) (H.map (P.inr (X := X)) ≫ liftStep T H R A)) := by
  intro A E
  let Q := T.monad
  let j : R.obj X ⟶ R.obj A := P.inr ≫ R.unit A
  let b : P.sum X E ⟶ R.obj A := P.desc (P.inl ≫ R.unit A)
    (H.map (P.inr (X := X)) ≫ liftStep T H R A)
  let c : P.sum X E ⟶ P.sum A (H.obj (R.obj A)) := P.map (P.inl (Y := R.obj X)) (H.map j)
  have hb : b ≫ R.out A = c ≫ Q.η.app (P.sum A (H.obj (R.obj A))) := by
    have hu : R.unit A ≫ R.out A = P.inl ≫ Q.η.app (P.sum A (H.obj (R.obj A))) := R.unit_out A
    simp only [b, Coproducts.desc_comp, Category.assoc, hu, liftStep_out, raise, c, Coproducts.map]
    exact congrArg (fun z => P.desc (P.inl ≫ P.inl ≫ Q.η.app (P.sum A (H.obj (R.obj A)))) z)
      (H.map_comp_assoc (P.inr (X := X) (Y := R.obj X)) (R.unit A) _).symm
  have hl : delayedBody T H R X ≫ R.out A = R.out X ≫ Q.map c := by
    change (R.out X ≫ Q.map c ≫ R.roll A) ≫ R.out A = _
    rw [Category.assoc, Category.assoc, R.roll_out]
    exact congrArg (R.out X ≫ ·) (Category.comp_id (Q.map c))
  have hr : (R.out X ≫ liftBase T H R (P.sum X E) ≫ R.extend P b) ≫ R.out A =
      R.out X ≫ Q.map c := by
    rw [Category.assoc, Category.assoc, liftBase_extend_out T H R, hb]
    change R.out X ≫ Q.map (c ≫ Q.η.app _) ≫ Q.μ.app _ = _
    simp
  change delayedBody T H R X = R.out X ≫ liftBase T H R (P.sum X E) ≫ R.extend P b
  have h := congrArg (· ≫ R.roll A) (hl.trans hr.symm)
  rw [Category.assoc, R.out_roll, Category.comp_id] at h
  simpa only [Category.assoc, R.out_roll, Category.comp_id] using h

theorem mediator_unique [HasInitial C] {S : GuardedElgotMonad P}
    (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)
    (m : GuardedElgotMonadHom P ((parametrizedElgot T H).resumptionElgotMonad R) S)
    (base : ∀ X, liftBase T H R X ≫ m.hom.app X = ξ.hom.app X)
    (step : ∀ X, liftStep T H R X ≫ m.hom.app X = σ.val.app X)
    (X : C) : m.hom.app X = (mediator R ξ σ X).of := by
  let M := parametrizedElgot T H
  let A := P.sum X (R.obj X)
  let E := H.obj (R.obj X)
  let Q := S.monad
  let K := P.kleisli Q
  let b : P.sum X E ⟶ R.obj A := P.desc (P.inl ≫ R.unit A)
    (H.map (P.inr (X := X)) ≫ liftStep T H R A)
  have hb : (delayedBody T H R X) ≫ m.hom.app A = (mediatorBody R ξ σ X).of := by
    have rb : R.extend P b ≫ m.hom.app A =
        m.hom.app (P.sum X E) ≫ Q.map (b ≫ m.hom.app A) ≫ Q.μ.app A :=
      (congrArg (· ≫ m.hom.app A) (R.monad_extend P b)).symm.trans (map_extension m.hom b)
    rw [delayed_body_generators T H R X]
    change (R.out X ≫ liftBase T H R (P.sum X E) ≫ R.extend P b) ≫ m.hom.app A = _
    rw [Category.assoc, Category.assoc, rb]
    have re : liftBase T H R (P.sum X E) ≫
        m.hom.app (P.sum X E) ≫ Q.map (b ≫ m.hom.app A) ≫ Q.μ.app A =
        ξ.hom.app (P.sum X E) ≫ Q.map (b ≫ m.hom.app A) ≫ Q.μ.app A := by
      rw [← Category.assoc, base]
    rw [re]
    have unit : R.unit A ≫ m.hom.app A = Q.η.app A := m.hom.app_η A
    have hm : H.map (P.inr (X := X) (Y := R.obj X)) ≫ σ.val.app A =
        σ.val.app (R.obj X) ≫ Q.map (P.inr (X := X) (Y := R.obj X)) :=
      σ.val.naturality _
    have eq : b ≫ m.hom.app A =
        P.desc (P.inl ≫ Q.η.app A) (σ.val.app (R.obj X) ≫ Q.map P.inr) := by
      simp only [b, Coproducts.desc_comp, Category.assoc, unit, step, hm]
    have ed : (K.desc K.inl (kleisliArrow (σ.val.app (R.obj X)) ≫ K.inr)).of =
        P.desc (P.inl ≫ Q.η.app A) (σ.val.app (R.obj X) ≫ Q.map P.inr) := by
      exact (kleisli_desc_of P Q _ _).trans
        (congrArg (fun g => P.desc (P.inl ≫ Q.η.app A) g)
          (comp_pure_of Q (kleisliArrow (σ.val.app (R.obj X))) P.inr))
    rw [eq, ← ed]
    change _ = (R.out X ≫ ξ.hom.app (P.sum X E)) ≫ Q.map _ ≫ Q.μ.app A
    simp only [Category.assoc]
    rfl
  let f := delayedBody T H R X
  have hf := (M.resumptionGuardedness_iff R
    (Y := Kleisli.mk (R.monad P) X) (Z := Kleisli.mk (R.monad P) (R.obj X))
    (kleisliArrow f)).mpr (delayed_guard T H R X)
  have eq := m.iteration f hf
  change M.iterateResumption R f (delayed_guard T H R X) ≫ m.hom.app X =
    (S.iteration.iterate (kleisliArrow (f ≫ m.hom.app A)) (m.guarded f hf)).of at eq
  rw [delayed_iteration T H R X, Category.id_comp] at eq
  exact eq.trans (congrArg (fun g : Kleisli.mk Q (R.obj X) ⟶ Kleisli.mk Q X => g.of)
    (iterate_congr S.iteration.toFixpoints (Kleisli.hom_ext hb) (m.guarded f hf)
      (mediatorBody_guarded R ξ σ X)))

end Silmaril.Calco2019.Proofs
