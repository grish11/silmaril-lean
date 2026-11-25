module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Defs
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

local notation "Q" => S.monad
local notation "K" => P.kleisli Q
local notation "J" => Kleisli.Adjunction.toKleisli Q

/-- A fully guarded computation stays guarded after an arbitrary continuation. -/
theorem post_guarded {A B Y Z : Kleisli Q} (f : A ⟶ B) (g : B ⟶ (K).sum Y Z)
    (h : S.guard.guarded (f ≫ (K).inr (X := Kleisli.mk Q (⊥_ C)))) :
    S.guard.guarded (f ≫ g) := by
  let l : Kleisli.mk Q (⊥_ C) ⟶ Y := (J).map (initial.to Y.of)
  have e := S.guard.compose g h (S.guard.trivial (Z := Z) l)
  simpa only [Category.assoc, Coproducts.inr_desc] using e

theorem mediatorBody_guarded (X : C) :
    S.guard.guarded (Y := Kleisli.mk Q X) (Z := Kleisli.mk Q (R.obj X)) (mediatorBody R ξ σ X) := by
  have h := post_guarded (kleisliArrow (σ.val.app (R.obj X)))
    ((K).inr (X := Kleisli.mk Q X) (Y := Kleisli.mk Q (R.obj X)))
    (Kleisli.hom_ext (comp_pure_of Q (kleisliArrow (σ.val.app (R.obj X))) P.inr) ▸
      σ.property (R.obj X))
  have i : S.guard.guarded (X := Kleisli.mk Q X) (Y := Kleisli.mk Q X)
      (Z := Kleisli.mk Q (R.obj X)) (K).inl := by
    simpa only [Category.id_comp] using S.guard.trivial (Z := Kleisli.mk Q (R.obj X)) (𝟙 (Kleisli.mk Q X))
  exact Guardedness.precomp (S.guard.parallel i h) _

@[expose]
noncomputable def mediator (X : C) : Kleisli.mk Q (R.obj X) ⟶ Kleisli.mk Q X :=
  S.iteration.iterate (mediatorBody R ξ σ X) (mediatorBody_guarded R ξ σ X)

theorem mediator_unfold (X : C) :
    mediator R ξ σ X =
      kleisliArrow (R.out X ≫ ξ.hom.app (P.sum X (H.obj (R.obj X)))) ≫
        (K).desc (𝟙 (Kleisli.mk Q X)) (kleisliArrow (σ.val.app (R.obj X)) ≫ mediator R ξ σ X) := by
  let a := kleisliArrow (R.out X ≫ ξ.hom.app (P.sum X (H.obj (R.obj X))))
  let s := kleisliArrow (σ.val.app (R.obj X))
  let m := mediator R ξ σ X
  have e := S.iteration.fixpoint (mediatorBody R ξ σ X) (mediatorBody_guarded R ξ σ X)
  change (a ≫ (K).desc (K).inl (s ≫ (K).inr)) ≫ (K).desc (𝟙 _) m = m at e
  simpa only [Category.assoc, Coproducts.desc_comp, Coproducts.inl_desc, Coproducts.inr_desc]
    using e.symm

theorem normalized_mediator {A X Y : C} (f : A ⟶ R.obj (P.sum Y X)) :
    let Z := P.sum Y X
    let W := R.obj Z
    let E := H.obj W
    let u := (f ≫ R.out Z) ≫ T.monad.map (rearrange P E (Y := Y) (Z := X))
    let v := (kleisliArrow (u ≫ ξ.hom.app (P.sum (P.sum Y E) X)) :
      Kleisli.mk Q A ⟶ Kleisli.mk Q (P.sum (P.sum Y E) X))
    (J).map f ≫ mediator R ξ σ Z =
      v ≫ (K).desc ((K).desc (K).inl (kleisliArrow (σ.val.app W) ≫ mediator R ξ σ Z)) (K).inr := by
  intro Z W E u v
  let k := (K)
  let y := Kleisli.mk Q Y
  let x := Kleisli.mk Q X
  let b := kleisliArrow (σ.val.app W) ≫ mediator R ξ σ Z
  let j := rearrange P E (Y := Y) (Z := X)
  let obs : Kleisli.mk Q W ⟶ k.sum (k.sum y x) (Kleisli.mk Q E) :=
    kleisliArrow (R.out Z ≫ ξ.hom.app (P.sum Z E))
  have n : v = ((J).map f ≫ obs) ≫ (J).map j := by
    apply Kleisli.hom_ext
    rw [comp_pure_of Q, pure_comp_of Q]
    change ((f ≫ R.out Z) ≫ T.monad.map j) ≫ ξ.hom.app (P.sum (P.sum Y E) X) =
      (f ≫ R.out Z ≫ ξ.hom.app (P.sum Z E)) ≫ (Q).map j
    simp only [Category.assoc, ξ.hom.toNatTrans.naturality]
    rfl
  have er : (J).map j ≫ k.desc (k.desc k.inl b) k.inr = k.desc (𝟙 (k.sum y x)) b := by
    apply Kleisli.hom_ext
    rw [pure_comp_of Q, kleisli_desc_of, kleisli_desc_of, kleisli_desc_of]
    change j ≫ P.desc (P.desc (k.inl (X := y) (Y := x)).of b.of) (k.inr (X := y) (Y := x)).of =
      P.desc ((Q).η.app Z) b.of
    simp [j, rearrange, Z]
    have e : P.desc (k.inl (X := y) (Y := x)).of (k.inr (X := y) (Y := x)).of = (Q).η.app Z := by
      apply P.hom_ext <;> simp only [Coproducts.inl_desc, Coproducts.inr_desc] <;> rfl
    rw [e]
  rw [n, Category.assoc, er, mediator_unfold R ξ σ Z]
  exact (Category.assoc _ _ _).symm

/-- The interpretation respects guarding in the observed right summand. -/
theorem mediator_guard {A Y Z : C} (f : A ⟶ R.obj (P.sum Y Z))
    (hf : (parametrizedElgot T H).ResumptionGuard R (Y := Y) (Z := Z) f) :
    S.guard.guarded (Y := Kleisli.mk Q Y) (Z := Kleisli.mk Q Z)
      ((J).map f ≫ mediator R ξ σ (P.sum Y Z)) := by
  let B := P.sum Y Z
  let E := H.obj (R.obj B)
  let y := Kleisli.mk Q Y
  let z := Kleisli.mk Q Z
  let e := Kleisli.mk Q E
  let r := Kleisli.mk Q (R.obj B)
  let k := (K)
  let j := rearrange P E (Y := Y) (Z := Z)
  let obs : A ⟶ T.monad.obj (P.sum B E) := f ≫ R.out B
  let normalized : Kleisli.mk Q A ⟶ k.sum (k.sum y e) z :=
    kleisliArrow ((obs ≫ T.monad.map j) ≫ ξ.hom.app (P.sum (P.sum Y E) Z))
  have hn : S.guard.guarded (Y := k.sum y e) (Z := z) normalized :=
    ξ.guarded (obs ≫ T.monad.map j) hf
  let s : e ⟶ r := kleisliArrow (σ.val.app (R.obj B))
  let b := s ≫ mediator R ξ σ B
  have hb : S.guard.guarded (Y := y) (Z := z) b :=
    post_guarded s (mediator R ξ σ B)
      (Kleisli.hom_ext (comp_pure_of Q s P.inr) ▸ σ.property (R.obj B))
  let i := k.inl (X := y) (Y := z)
  let t := k.inr (X := y) (Y := z)
  have hi : S.guard.guarded (Y := y) (Z := z) i := by
    simpa only [Category.id_comp] using S.guard.trivial (Z := z) (𝟙 y)
  have g := S.guard.compose t hn (S.guard.parallel hi hb)
  have eq : (J).map f ≫ mediator R ξ σ B = normalized ≫ k.desc (k.desc i b) t :=
    normalized_mediator R ξ σ f
  exact eq.symm ▸ g

theorem mediator_base (X : C) :
    (J).map (liftBase T H R X) ≫ mediator R ξ σ X = kleisliArrow (ξ.hom.app X) := by
  let E := H.obj (R.obj X)
  let A := P.sum X E
  let a : Kleisli.mk Q (R.obj X) ⟶ Kleisli.mk Q A :=
    kleisliArrow (R.out X ≫ ξ.hom.app A)
  let b := (K).desc (𝟙 (Kleisli.mk Q X))
    (kleisliArrow (σ.val.app (R.obj X)) ≫ mediator R ξ σ X)
  have h : (J).map (liftBase T H R X) ≫ a = kleisliArrow (ξ.hom.app X) ≫ (K).inl := by
    apply Kleisli.hom_ext
    exact (pure_comp_of Q (liftBase T H R X) a).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ ξ.hom.app A) (liftBase_out T H R X)).trans
          ((ξ.hom.toNatTrans.naturality (P.inl (Y := E))).trans
            (comp_pure_of Q (kleisliArrow (ξ.hom.app X)) P.inl).symm)))
  rw [mediator_unfold R ξ σ X]
  change (J).map (liftBase T H R X) ≫ a ≫ b = _
  rw [← Category.assoc, h, Category.assoc]
  have e : (K).inl ≫ b = 𝟙 (Kleisli.mk Q X) := (K).inl_desc _ _
  rw [e, Category.comp_id]

theorem mediator_unit (X : C) :
    (J).map (R.unit X) ≫ mediator R ξ σ X = 𝟙 (Kleisli.mk Q X) := by
  have e : T.monad.η.app X ≫ liftBase T H R X = R.unit X := by
    rw [← baseEmbedding_app]
    exact (baseEmbedding T H R).hom.app_η X
  rw [← e, (J).map_comp, Category.assoc, mediator_base R ξ σ X]
  apply Kleisli.hom_ext
  exact (pure_comp_of Q (T.monad.η.app X) (kleisliArrow (ξ.hom.app X))).trans (ξ.hom.app_η X)

theorem mediator_step (X : C) :
    (J).map (liftStep T H R X) ≫ mediator R ξ σ X = kleisliArrow (σ.val.app X) := by
  let E := H.obj (R.obj X)
  let A := P.sum X E
  let a : Kleisli.mk Q (R.obj X) ⟶ Kleisli.mk Q A :=
    kleisliArrow (R.out X ≫ ξ.hom.app A)
  let b := (K).desc (𝟙 (Kleisli.mk Q X))
    (kleisliArrow (σ.val.app (R.obj X)) ≫ mediator R ξ σ X)
  have h : (J).map (liftStep T H R X) ≫ a = (J).map (H.map (R.unit X)) ≫ (K).inr := by
    apply Kleisli.hom_ext
    rw [pure_comp_of Q, pure_comp_of Q]
    change liftStep T H R X ≫ R.out X ≫ ξ.hom.app A =
      H.map (R.unit X) ≫ P.inr ≫ (Q).η.app A
    have base : T.monad.η.app A ≫ ξ.hom.app A = (Q).η.app A := ξ.hom.app_η A
    rw [← Category.assoc, liftStep_out]
    simp only [raise, Category.assoc]
    change H.map (R.unit X) ≫ P.inr ≫ T.monad.η.app A ≫ ξ.hom.app A =
      H.map (R.unit X) ≫ P.inr ≫ (Q).η.app A
    rw [base]
  have n : (J).map (H.map (R.unit X)) ≫ kleisliArrow (σ.val.app (R.obj X)) =
      kleisliArrow (σ.val.app X) ≫ (J).map (R.unit X) :=
    Kleisli.hom_ext ((pure_comp_of Q _ _).trans
      ((σ.val.naturality (R.unit X)).trans (comp_pure_of Q _ _).symm))
  rw [mediator_unfold R ξ σ X]
  change (J).map (liftStep T H R X) ≫ a ≫ b = _
  rw [← Category.assoc, h, Category.assoc]
  change (J).map (H.map (R.unit X)) ≫ (K).inr ≫
    (K).desc (𝟙 (Kleisli.mk Q X)) (kleisliArrow (σ.val.app (R.obj X)) ≫ mediator R ξ σ X) = _
  rw [Coproducts.inr_desc, ← Category.assoc, n, Category.assoc, mediator_unit R ξ σ X, Category.comp_id]

private theorem mediatorBody_natural {X Y : C} (f : X ⟶ Y) :
    (J).map ((R.monad P).map f) ≫ mediatorBody R ξ σ Y =
      mediatorBody R ξ σ X ≫ (K).map ((J).map f) ((J).map ((R.monad P).map f)) := by
  let g : R.obj X ⟶ R.obj Y := (R.monad P).map f
  let x := Kleisli.mk Q X
  let y := Kleisli.mk Q Y
  let u := Kleisli.mk Q (R.obj X)
  let v := Kleisli.mk Q (R.obj Y)
  let e := Kleisli.mk Q (H.obj (R.obj X))
  let e' := Kleisli.mk Q (H.obj (R.obj Y))
  let a : u ⟶ (K).sum x e := kleisliArrow (R.out X ≫ ξ.hom.app (P.sum X (H.obj (R.obj X))))
  let a' : v ⟶ (K).sum y e' := kleisliArrow (R.out Y ≫ ξ.hom.app (P.sum Y (H.obj (R.obj Y))))
  let b : e ⟶ u := kleisliArrow (σ.val.app (R.obj X))
  let b' : e' ⟶ v := kleisliArrow (σ.val.app (R.obj Y))
  let m := P.map f (H.map g)
  have ha : (J).map g ≫ a' = a ≫ (K).map ((J).map f) ((J).map (H.map g)) := by
    rw [kleisli_map_pure]
    apply Kleisli.hom_ext
    rw [pure_comp_of Q, comp_pure_of Q]
    change g ≫ R.out Y ≫ ξ.hom.app _ = (R.out X ≫ ξ.hom.app _) ≫ (Q).map m
    rw [← Category.assoc, show g ≫ R.out Y = R.out X ≫ T.monad.map m from
      resumption_map_out T H R f, Category.assoc, ξ.hom.toNatTrans.naturality, Category.assoc]
  have hb : (J).map (H.map g) ≫ b' = b ≫ (J).map g :=
    Kleisli.hom_ext ((pure_comp_of Q _ _).trans
      ((σ.val.naturality g).trans (comp_pure_of Q _ _).symm))
  have hdesc : (K).map ((J).map f) ((J).map (H.map g)) ≫ (K).desc (K).inl (b' ≫ (K).inr) =
      (K).desc (K).inl (b ≫ (K).inr) ≫ (K).map ((J).map f) ((J).map g) := by
    apply (K).hom_ext
    · simp [Coproducts.map, Category.assoc]
    · simp [Coproducts.map, Category.assoc, ← reassoc_of% hb]
  change (J).map g ≫ a' ≫ (K).desc (K).inl (b' ≫ (K).inr) =
    (a ≫ (K).desc (K).inl (b ≫ (K).inr)) ≫ (K).map ((J).map f) ((J).map g)
  rw [← Category.assoc, ha, Category.assoc, hdesc, Category.assoc]

theorem mediator_natural {X Y : C} (f : X ⟶ Y) :
    (J).map ((R.monad P).map f) ≫ mediator R ξ σ Y =
      mediator R ξ σ X ≫ (J).map f := by
  let x := Kleisli.mk Q (R.obj X)
  let y := Kleisli.mk Q Y
  let g : R.obj X ⟶ R.obj Y := (R.monad P).map f
  let a := mediatorBody R ξ σ X
  let a' := mediatorBody R ξ σ Y
  let b := a ≫ (K).map ((J).map f) (𝟙 x)
  have ha := mediatorBody_guarded R ξ σ X
  have ha' := mediatorBody_guarded R ξ σ Y
  have hb := Guardedness.map ha ((J).map f) (𝟙 x)
  have d : (K).map ((J).map f) (𝟙 x) ≫ (K).map (𝟙 y) ((J).map g) =
      (K).map ((J).map f) ((J).map g) := by
    apply (K).hom_ext
    · simp [Coproducts.map, Category.assoc]
      exact congrArg ((J).map f ≫ ·) (Category.id_comp _)
    · simp [Coproducts.map, Category.assoc]
  have e : (J).map g ≫ a' = b ≫ (K).map (𝟙 y) ((J).map g) := by
    change _ = (_ ≫ _) ≫ _
    rw [Category.assoc, d]
    exact mediatorBody_natural R ξ σ f
  exact (S.uniformity a' b g ha' hb e).trans
    (S.iteration.naturalCodiagonal.naturality a ((J).map f) ha hb)

end Silmaril.Calco2019.Proofs
