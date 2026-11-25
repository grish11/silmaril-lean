module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Thms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

section Triangular

variable {K : Type u} [Category.{v} K] {P : Coproducts K}
  {G : Guardedness P} (F : G.Fixpoints)
  (N : F.NaturalCodiagonal) (U : F.CoproductUniformity)
  {A B X Y : K}

private theorem triangle_comp {Y' D : K} (f : D ⟶ P.sum Y' D)
    (g : D ⟶ P.sum Y' D) (e : f = g) (hf : G.guarded f) (hg : G.guarded g) :
    F.iterate f hf = F.iterate g hg := by
  subst g
  rfl

include N U in
private theorem triangular (a : A ⟶ P.sum X A) (h : X ⟶ P.sum Y B) (b : B ⟶ P.sum Y B)
    (ha : G.guarded a) (hh : G.guarded h) (hb : G.guarded b)
    (ht : G.guarded (Y := Y) (Z := P.sum A B) (P.desc
      (a ≫ P.desc (h ≫ P.map (𝟙 Y) P.inr) (P.inl ≫ P.inr))
      (b ≫ P.map (𝟙 Y) P.inr))) :
    P.inl ≫ F.iterate (P.desc
      (a ≫ P.desc (h ≫ P.map (𝟙 Y) P.inr) (P.inl ≫ P.inr))
      (b ≫ P.map (𝟙 Y) P.inr)) ht = F.iterate a ha ≫ h ≫ P.desc (𝟙 Y) (F.iterate b hb) := by
  let D := P.sum A B
  let E := P.sum Y D
  let i : A ⟶ D := P.inl
  let j : B ⟶ D := P.inr
  let l := h ≫ P.map (𝟙 Y) j
  let v := b ≫ P.map (𝟙 Y) j
  let c := a ≫ P.map l (𝟙 A)
  let d := P.desc (a ≫ P.map l i) (v ≫ P.inl (Y := D))
  let t := P.desc (a ≫ P.desc l (i ≫ P.inr)) v
  have hl : G.guarded (Y := Y) (Z := D) l := Guardedness.map hh _ _
  have hv : G.guarded (Y := Y) (Z := D) v := Guardedness.map hb _ _
  have hc : G.guarded (Y := E) (Z := A) c := Guardedness.map ha _ _
  have hdi : d ≫ P.assoc (X := Y) (Y := D) (Z := D) =
      P.desc (a ≫ P.desc (l ≫ P.map (𝟙 Y) (P.inl (X := D) (Y := D))) (i ≫ P.inr ≫ P.inr))
        (v ≫ P.map (𝟙 Y) (P.inl (X := D) (Y := D))) := by
    change P.desc (a ≫ P.map l i) (v ≫ P.inl) ≫ P.assoc = _
    simp [Coproducts.assoc, Coproducts.map, Category.assoc]
  have hn : G.nested (Y := Y) (Z := D) (W := D) d := by
    change G.guarded (d ≫ P.assoc (X := Y) (Y := D) (Z := D))
    rw [hdi]
    exact G.parallel
      (G.compose _ ha (Guardedness.map hl (𝟙 Y) (P.inl (X := D) (Y := D))))
      (Guardedness.map hv (𝟙 Y) (P.inl (X := D) (Y := D)))
  have hi : G.guarded (Y := E) (Z := D) d := Guardedness.weaken hn
  have idi : i ≫ d = c ≫ P.map (𝟙 E) i := by
    change P.inl ≫ P.desc (a ≫ P.map l i) (v ≫ P.inl) = _
    simp [c, E, Coproducts.map, Category.assoc]
  let k := F.iterate d hi
  have kl : i ≫ k = F.iterate a ha ≫ l :=
    (U.inl d c hi hc idi).trans (N.naturality a l ha hc)
  have kr : j ≫ k = v := by
    have e := congrArg (j ≫ ·) (F.fixpoint d hi)
    change j ≫ (d ≫ P.desc (𝟙 E) k) = j ≫ k at e
    simpa [d, E, j, Category.assoc] using e.symm
  have hk : G.guarded (Y := Y) (Z := D) k := Guardedness.guarded_fixpoint hn (F.fixpoint d hi)
  let p := F.iterate k hk
  have pr : j ≫ p = F.iterate b hb := U.inr k b hk hb kr
  have pl : i ≫ p = F.iterate a ha ≫ h ≫ P.desc (𝟙 Y) (F.iterate b hb) := by
    have e := congrArg (i ≫ ·) (F.fixpoint k hk)
    change i ≫ (k ≫ P.desc (𝟙 Y) p) = i ≫ p at e
    rw [← Category.assoc, kl, Category.assoc, Category.assoc, P.map_desc, Category.id_comp, pr] at e
    exact e.symm
  have dm : d ≫ P.merge = t := by
    change P.desc (a ≫ P.map l i) (v ≫ P.inl) ≫ P.merge = P.desc (a ≫ P.desc l _) v
    simp [Coproducts.merge, Category.assoc]
  exact (congrArg (P.inl ≫ ·) (triangle_comp F t (d ≫ P.merge) dm.symm ht
    (Guardedness.merge hn))).trans
      ((congrArg (P.inl ≫ ·) (N.codiagonal d hn hi hk (Guardedness.merge hn))).trans pl)

end Triangular

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

local notation "Q" => S.monad
local notation "K" => P.kleisli Q
local notation "J" => Kleisli.Adjunction.toKleisli Q

private noncomputable def observe (X : C) :
    Kleisli.mk Q (R.obj X) ⟶ (K).sum (Kleisli.mk Q X) (Kleisli.mk Q (H.obj (R.obj X))) :=
  kleisliArrow (R.out X ≫ ξ.hom.app (P.sum X (H.obj (R.obj X))))

omit [HasInitial C] in
private theorem observe_extend {X Y : C} (f : X ⟶ R.obj Y) :
    (J).map (R.extend P f) ≫ observe R ξ Y =
      observe R ξ X ≫ (K).desc ((J).map f ≫ observe R ξ Y)
        ((J).map (H.map (R.extend P f) ≫ P.inr (X := Y))) := by
  let A := H.obj (R.obj X)
  let B := H.obj (R.obj Y)
  let U := P.sum X A
  let V := P.sum Y B
  let k := R.extend P f
  let q := H.map k
  let c := P.desc (f ≫ R.out Y) (raise P T.monad B Y)
  let d := P.map (𝟙 X) q ≫ c
  let h := (K).desc ((J).map f ≫ observe R ξ Y) ((J).map (q ≫ P.inr (X := Y)))
  have c_eq : d = P.desc (f ≫ R.out Y) (q ≫ raise P T.monad B Y) := by
    simp [d, c]
  have h_eq : h.of = d ≫ ξ.hom.app V := by
    change ((K).desc ((J).map f ≫ observe R ξ Y) ((J).map (q ≫ P.inr (X := Y)))).of = _
    rw [kleisli_desc_of, pure_comp_of, c_eq, P.desc_comp]
    change P.desc (f ≫ R.out Y ≫ ξ.hom.app V) ((q ≫ P.inr) ≫ (Q).η.app V) =
      P.desc ((f ≫ R.out Y) ≫ ξ.hom.app V) ((q ≫ (P.inr ≫ T.monad.η.app V)) ≫ ξ.hom.app V)
    have unit : T.monad.η.app V ≫ ξ.hom.app V = (Q).η.app V := ξ.hom.app_η V
    simp only [Category.assoc, unit]
  have out_eq : k ≫ R.out Y = R.out X ≫ T.monad.map d ≫ T.monad.μ.app V := by
    have e := R.extend_spec P f
    change k ≫ R.out Y = R.out X ≫ T.monad.map (P.map (𝟙 X) q) ≫
      ((parametrizedElgot T H).toParametrizedMonad.extend (W := R.obj Y) (f ≫ R.out Y)) at e
    have ext_eq : (parametrizedElgot T H).toParametrizedMonad.extend (W := R.obj Y) (f ≫ R.out Y) =
        T.monad.map c ≫ T.monad.μ.app V :=
      family_extend P T.monad B (f ≫ R.out Y)
    rw [ext_eq] at e
    simpa only [d, Category.assoc, Functor.map_comp] using e
  apply Kleisli.hom_ext
  rw [pure_comp_of Q]
  change k ≫ R.out Y ≫ ξ.hom.app V =
    (R.out X ≫ ξ.hom.app U) ≫ (Q).map h.of ≫ (Q).μ.app V
  calc
    k ≫ R.out Y ≫ ξ.hom.app V =
        R.out X ≫ (T.monad.map d ≫ T.monad.μ.app V) ≫ ξ.hom.app V := by
      rw [← Category.assoc, out_eq, Category.assoc]
    _ = R.out X ≫ ξ.hom.app U ≫ (Q).map h.of ≫ (Q).μ.app V :=
      congrArg (R.out X ≫ ·) ((map_extension ξ.hom d).trans
        (congrArg (fun c' => ξ.hom.app U ≫ (Q).map c' ≫ (Q).μ.app V) h_eq.symm))
    _ = _ := (Category.assoc _ _ _).symm

theorem mediatorBody_extend {X Y : C} (f : X ⟶ R.obj Y) :
    (J).map (R.extend P f) ≫ mediatorBody R ξ σ Y =
      mediatorBody R ξ σ X ≫ (K).desc ((J).map f ≫ mediatorBody R ξ σ Y)
        ((J).map (R.extend P f) ≫ (K).inr) := by
  let k := R.extend P f
  let x := Kleisli.mk Q X
  let y := Kleisli.mk Q Y
  let a := Kleisli.mk Q (R.obj X)
  let b := Kleisli.mk Q (R.obj Y)
  let sx : Kleisli.mk Q (H.obj (R.obj X)) ⟶ a := kleisliArrow (σ.val.app (R.obj X))
  let sy : Kleisli.mk Q (H.obj (R.obj Y)) ⟶ b := kleisliArrow (σ.val.app (R.obj Y))
  let dx := (K).desc ((K).inl (X := x) (Y := a)) (sx ≫ (K).inr)
  let dy := (K).desc ((K).inl (X := y) (Y := b)) (sy ≫ (K).inr)
  have nat : (J).map (H.map k) ≫ sy = sx ≫ (J).map k :=
    Kleisli.hom_ext ((pure_comp_of Q _ _).trans
      ((σ.val.naturality k).trans (comp_pure_of Q _ _).symm))
  change (J).map k ≫ observe R ξ Y ≫ dy =
    (observe R ξ X ≫ dx) ≫ (K).desc ((J).map f ≫ (observe R ξ Y ≫ dy)) ((J).map k ≫ (K).inr)
  rw [← Category.assoc, observe_extend R ξ f]
  have jcomp : (J).map (H.map k ≫ P.inr (X := Y)) =
      (J).map (H.map k) ≫ (K).inr :=
    (J).map_comp _ _
  rw [jcomp]
  simp only [dx, dy, Category.assoc, Coproducts.desc_comp, Coproducts.inl_desc,
    Coproducts.inr_desc, ← reassoc_of% nat]

theorem mediator_extend {X Y : C} (f : X ⟶ R.obj Y) :
    (J).map (R.extend P f) ≫ mediator R ξ σ Y =
      mediator R ξ σ X ≫ (((J).map f) ≫ mediator R ξ σ Y) := by
  let y := Kleisli.mk Q Y
  let a := mediatorBody R ξ σ X
  let b := mediatorBody R ξ σ Y
  let h := (J).map f ≫ b
  let i := (K).inl (X := Kleisli.mk Q (R.obj X)) (Y := Kleisli.mk Q (R.obj Y))
  let j := (K).inr (X := Kleisli.mk Q (R.obj X)) (Y := Kleisli.mk Q (R.obj Y))
  let k := R.extend P f
  let q := P.desc k (𝟙 (R.obj Y))
  let t := (K).desc (a ≫ (K).desc (h ≫ (K).map (𝟙 y) j) (i ≫ (K).inr))
    (b ≫ (K).map (𝟙 y) j)
  have ha := mediatorBody_guarded R ξ σ X
  have hb := mediatorBody_guarded R ξ σ Y
  have hh := Guardedness.precomp hb ((J).map f)
  have ht : S.guard.guarded (Y := y) (Z := (K).sum (Kleisli.mk Q (R.obj X)) (Kleisli.mk Q (R.obj Y))) t :=
    S.guard.parallel (S.guard.compose _ ha (Guardedness.map hh _ _)) (Guardedness.map hb _ _)
  have eqi : i ≫ (J).map q = (J).map k :=
    ((J).map_comp P.inl q).symm.trans (congrArg (J).map (P.inl_desc _ _))
  have eqj : j ≫ (J).map q = 𝟙 (Kleisli.mk Q (R.obj Y)) :=
    ((J).map_comp P.inr q).symm.trans ((congrArg (J).map (P.inr_desc _ _)).trans ((J).map_id _))
  have maps : (K).map (𝟙 y) j ≫ (K).map (𝟙 y) ((J).map q) =
      𝟙 ((K).sum y (Kleisli.mk Q (R.obj Y))) := by
    apply (K).hom_ext
    · simp [Coproducts.map, Category.assoc]
    · simpa [Coproducts.map, Category.assoc] using congrArg (· ≫ (K).inr (X := y)) eqj
  have sq : (J).map q ≫ b = t ≫ (K).map (𝟙 y) ((J).map q) := by
    refine (K).hom_ext (X := Kleisli.mk Q (R.obj X)) (Y := Kleisli.mk Q (R.obj Y)) ?_ ?_
    · change i ≫ (J).map q ≫ b = i ≫ t ≫ (K).map (𝟙 y) ((J).map q)
      have ti : i ≫ t = a ≫ (K).desc (h ≫ (K).map (𝟙 y) j) (i ≫ (K).inr) :=
        (K).inl_desc _ _
      rw [← Category.assoc i, eqi, ← Category.assoc i, ti, mediatorBody_extend R ξ σ]
      rw [Category.assoc a, Coproducts.desc_comp]
      have hr : (h ≫ (K).map (𝟙 y) j) ≫ (K).map (𝟙 y) ((J).map q) = h := by
        rw [Category.assoc, maps, Category.comp_id]
      have hs : (i ≫ (K).inr) ≫ (K).map (𝟙 y) ((J).map q) = (J).map k ≫ (K).inr := by
        rw [Category.assoc]
        change i ≫ (K).inr ≫ (K).desc ((𝟙 y) ≫ (K).inl) ((J).map q ≫ (K).inr) = _
        rw [Coproducts.inr_desc, ← Category.assoc i, eqi]
      rw [hr, hs]
    · change j ≫ (J).map q ≫ b = j ≫ t ≫ (K).map (𝟙 y) ((J).map q)
      have tj : j ≫ t = b ≫ (K).map (𝟙 y) j := (K).inr_desc _ _
      rw [← Category.assoc j, eqj, ← Category.assoc j, tj, Category.assoc, maps,
        Category.id_comp, Category.comp_id]
  let F := S.iteration.toFixpoints
  have U := F.coproductUniformity_of_uniform (P.kleisliPreservesSelected Q) (fun Z => ⟨Z.of, rfl⟩) S.uniformity
  have selected : (J).map q ≫ mediator R ξ σ Y = F.iterate t ht :=
    S.uniformity b t q hb ht sq
  have tri := triangular F S.iteration.naturalCodiagonal U a h b ha hh hb ht
  have fix := S.iteration.fixpoint b hb
  change b ≫ (K).desc (𝟙 y) (mediator R ξ σ Y) = mediator R ξ σ Y at fix
  calc
    (J).map k ≫ mediator R ξ σ Y = i ≫ F.iterate t ht := by
      rw [← eqi, Category.assoc, selected]
    _ = mediator R ξ σ X ≫ ((J).map f ≫ mediator R ξ σ Y) := by
      have e : i ≫ F.iterate t ht =
          mediator R ξ σ X ≫ h ≫ (K).desc (𝟙 y) (mediator R ξ σ Y) := tri
      exact e.trans (by simp only [h, Category.assoc, fix])


theorem mediator_natural_of {X Y : C} (f : X ⟶ Y) :
    (R.monad P).map f ≫ (mediator R ξ σ Y).of =
      (mediator R ξ σ X).of ≫ (Q).map f :=
  (pure_comp_of Q _ _).symm.trans
    ((congrArg Kleisli.Hom.of (mediator_natural R ξ σ f)).trans (comp_pure_of Q _ _))

theorem mediator_unit_of (X : C) :
    R.unit X ≫ (mediator R ξ σ X).of = (Q).η.app X :=
  (pure_comp_of Q _ _).symm.trans (congrArg Kleisli.Hom.of (mediator_unit R ξ σ X))

theorem mediator_mul (X : C) :
    (R.monad P).μ.app X ≫ (mediator R ξ σ X).of =
      ((R.monad P).map (mediator R ξ σ X).of ≫ (mediator R ξ σ ((Q).obj X)).of) ≫ (Q).μ.app X := by
  let m := (mediator R ξ σ X).of
  let n := (mediator R ξ σ (R.obj X)).of
  have e := mediator_extend R ξ σ (𝟙 (R.obj X))
  rw [show (J).map (𝟙 (R.obj X)) = 𝟙 (Kleisli.mk Q (R.obj X)) from (J).map_id _,
    Category.id_comp] at e
  have he : R.extend P (𝟙 (R.obj X)) ≫ m = n ≫ (Q).map m ≫ (Q).μ.app X :=
    (pure_comp_of Q _ _).symm.trans (congrArg Kleisli.Hom.of e)
  change R.extend P (𝟙 (R.obj X)) ≫ m =
    ((R.monad P).map m ≫ (mediator R ξ σ ((Q).obj X)).of) ≫ (Q).μ.app X
  rw [he, ← Category.assoc n, ← mediator_natural_of R ξ σ m]

end Silmaril.Calco2019.Proofs
