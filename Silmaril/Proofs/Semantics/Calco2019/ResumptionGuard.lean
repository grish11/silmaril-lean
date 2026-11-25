module

public import Silmaril.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

@[reassoc]
theorem pure_comp_of (T : CategoryTheory.Monad C) {X Y Z : C} (f : X ⟶ Y)
    (g : Kleisli.mk T Y ⟶ Kleisli.mk T Z) :
    (((Kleisli.Adjunction.toKleisli T).map f) ≫ g).of = f ≫ g.of := by
  change (f ≫ T.η.app Y) ≫ T.map g.of ≫ T.μ.app Z = f ≫ g.of
  simp [Category.assoc, ← T.η.naturality_assoc g.of]

theorem comp_pure_of (T : CategoryTheory.Monad C) {X Y Z : C}
    (f : Kleisli.mk T X ⟶ Kleisli.mk T Y) (g : Y ⟶ Z) :
    (f ≫ ((Kleisli.Adjunction.toKleisli T).map g)).of = f.of ≫ T.map g := by
  change f.of ≫ T.map (g ≫ T.η.app Z) ≫ T.μ.app Z = f.of ≫ T.map g
  simp

theorem kleisli_desc_of (P : Coproducts C) (T : CategoryTheory.Monad C)
    {X Y Z : Kleisli T} (f : X ⟶ Z) (g : Y ⟶ Z) :
    ((P.kleisli T).desc f g).of = P.desc f.of g.of := by
  apply P.hom_ext
  · exact (pure_comp_of T P.inl ((P.kleisli T).desc f g)).symm.trans
      ((congrArg Kleisli.Hom.of ((P.kleisli T).inl_desc f g)).trans (P.inl_desc f.of g.of).symm)
  · exact (pure_comp_of T P.inr ((P.kleisli T).desc f g)).symm.trans
      ((congrArg Kleisli.Hom.of ((P.kleisli T).inr_desc f g)).trans (P.inr_desc f.of g.of).symm)

theorem kleisli_map_pure (T : CategoryTheory.Monad C) {X Y V W : C}
    (f : X ⟶ V) (g : Y ⟶ W) :
    (P.kleisli T).map ((Kleisli.Adjunction.toKleisli T).map f)
        ((Kleisli.Adjunction.toKleisli T).map g) =
      (Kleisli.Adjunction.toKleisli T).map (P.map f g) := by
  let J := Kleisli.Adjunction.toKleisli T
  apply (P.kleisli T).hom_ext
  · calc
      _ = J.map f ≫ J.map (P.inl (Y := W)) :=
        (P.kleisli T).inl_desc _ _
      _ = J.map (f ≫ P.inl) := (J.map_comp _ _).symm
      _ = J.map (P.inl ≫ P.map f g) := congrArg J.map (P.inl_desc _ _).symm
      _ = _ := J.map_comp _ _
  · calc
      _ = J.map g ≫ J.map (P.inr (X := V)) :=
        (P.kleisli T).inr_desc _ _
      _ = J.map (g ≫ P.inr) := (J.map_comp _ _).symm
      _ = J.map (P.inr ≫ P.map f g) := congrArg J.map (P.inr_desc _ _).symm
      _ = _ := J.map_comp _ _

theorem map_extension {Q S : CategoryTheory.Monad C} (m : Q ⟶ S)
    {X Y : C} (g : X ⟶ Q.obj Y) :
    (Q.map g ≫ Q.μ.app Y) ≫ m.app Y =
      m.app X ≫ S.map (g ≫ m.app Y) ≫ S.μ.app Y := by
  rw [Category.assoc, m.app_μ]
  calc
    Q.map g ≫ (Q.map (m.app Y) ≫ m.app (S.obj Y)) ≫ S.μ.app Y =
        Q.map (g ≫ m.app Y) ≫ m.app (S.obj Y) ≫ S.μ.app Y := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [m.toNatTrans.naturality_assoc]

/-- Mapping the result of a resumption maps the first observation and its continuations. -/
@[reassoc]
theorem map_outOf {M : ParametrizedMonad C}
    (R : FinalResumptions M) (P : Coproducts C) {X Y : C} (g : X ⟶ Y) :
    (R.monad P).map g ≫ R.out Y =
      R.out X ≫ (M.parameter X).map ((R.monad P).map g) ≫ (M.obj (R.obj Y)).map g := by
  change R.extend P (g ≫ R.unit Y) ≫ R.out Y = _
  rw [R.extend_spec, Category.assoc, R.unit_out]
  simp only [ParametrizedMonad.extend, Functor.map_comp, Category.assoc,
    CategoryTheory.Monad.right_unit, Category.comp_id]
  rfl

section Guard

variable {M : ParametrizedMonad C} (G : M.Guards P)

private theorem guardAt_trivial (W : C) {X Y Z : C} (f : X ⟶ (M.obj W).obj Y) :
    G.guardedAt W (Y := Y) (Z := Z) (f ≫ (M.obj W).map P.inl) := by
  have h := (G.guard W).trivial (Z := Kleisli.mk (M.obj W) Z) (kleisliArrow f)
  have e := Kleisli.hom_ext (comp_pure_of _ (kleisliArrow f) (P.inl (Y := Z)))
  exact Eq.mp (congrArg ((G.guard W).guarded
    (Y := Kleisli.mk (M.obj W) Y) (Z := Kleisli.mk (M.obj W) Z)) e) h

private theorem guardAt_parallel (W : C) {X X' Y Z : C}
    {f : X ⟶ (M.obj W).obj (P.sum Y Z)} {g : X' ⟶ (M.obj W).obj (P.sum Y Z)}
    (hf : G.guardedAt W (Y := Y) (Z := Z) f) (hg : G.guardedAt W (Y := Y) (Z := Z) g) :
    G.guardedAt W (Y := Y) (Z := Z) (P.desc f g) := by
  have h := (G.guard W).parallel hf hg
  have e := Kleisli.hom_ext (kleisli_desc_of P _ (kleisliArrow f) (kleisliArrow g))
  exact Eq.mp (congrArg ((G.guard W).guarded
    (Y := Kleisli.mk (M.obj W) Y) (Z := Kleisli.mk (M.obj W) Z)) e) h

private theorem guardAt_compose (W : C) {X Y Z A B : C}
    {f : X ⟶ (M.obj W).obj (P.sum Y Z)} {g : Y ⟶ (M.obj W).obj (P.sum A B)}
    (h : Z ⟶ (M.obj W).obj (P.sum A B))
    (hf : G.guardedAt W (Y := Y) (Z := Z) f) (hg : G.guardedAt W (Y := A) (Z := B) g) :
    G.guardedAt W (Y := A) (Z := B) (f ≫ M.extend (W := W) (P.desc g h)) := by
  have h' := (G.guard W).compose (kleisliArrow h) hf hg
  have e : (kleisliArrow f ≫ (P.kleisli (M.obj W)).desc (kleisliArrow g) (kleisliArrow h)) =
      kleisliArrow (f ≫ M.extend (W := W) (P.desc g h)) := by
    apply Kleisli.hom_ext
    change f ≫ M.extend (W := W) (((P.kleisli (M.obj W)).desc
      (kleisliArrow g) (kleisliArrow h)).of) = _
    rw [kleisli_desc_of]
  exact Eq.mp (congrArg ((G.guard W).guarded
    (Y := Kleisli.mk (M.obj W) A) (Z := Kleisli.mk (M.obj W) B)) e) h'

private theorem guardAt_parameterOf {W V X Y Z : C} (k : W ⟶ V)
    {f : X ⟶ (M.obj W).obj (P.sum Y Z)} (hf : G.guardedAt W (Y := Y) (Z := Z) f) :
    G.guardedAt V (Y := Y) (Z := Z) (f ≫ (M.parameter (P.sum Y Z)).map k) :=
  G.preserves k f hf

variable (R : FinalResumptions M)

theorem resumptionGuard_trivial {X Y Z : C} (f : X ⟶ R.obj Y) :
    G.ResumptionGuard R (Y := Y) (Z := Z) (f ≫ (R.monad P).map P.inl) := by
  let i : Y ⟶ P.sum Y Z := P.inl
  let a := (f ≫ R.out Y) ≫ (M.parameter Y).map ((R.monad P).map i)
  have e : (f ≫ (R.monad P).map i) ≫ R.out (P.sum Y Z) =
      a ≫ (M.obj (R.obj (P.sum Y Z))).map i :=
    (Category.assoc _ _ _).trans ((congrArg (fun j => f ≫ j) (map_outOf R P i)).trans
      ((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm))
  exact Eq.mpr (congrArg (G.guardedAt (R.obj (P.sum Y Z)) (Y := Y) (Z := Z)) e)
    (guardAt_trivial G _ a)

theorem resumptionGuard_parallel {X X' Y Z : C}
    {f : X ⟶ R.obj (P.sum Y Z)} {g : X' ⟶ R.obj (P.sum Y Z)}
    (hf : G.ResumptionGuard R (Y := Y) (Z := Z) f)
    (hg : G.ResumptionGuard R (Y := Y) (Z := Z) g) :
    G.ResumptionGuard R (Y := Y) (Z := Z) (P.desc f g) := by
  exact Eq.mpr (congrArg (G.guardedAt (R.obj (P.sum Y Z)) (Y := Y) (Z := Z))
    (P.desc_comp f g (R.out (P.sum Y Z)))) (guardAt_parallel G _ hf hg)

theorem resumptionGuard_compose {X Y Z A B : C}
    {f : X ⟶ R.obj (P.sum Y Z)} {g : Y ⟶ R.obj (P.sum A B)}
    (h : Z ⟶ R.obj (P.sum A B))
    (hf : G.ResumptionGuard R (Y := Y) (Z := Z) f)
    (hg : G.ResumptionGuard R (Y := A) (Z := B) g) :
    G.ResumptionGuard R (Y := A) (Z := B) (f ≫ R.extend P (P.desc g h)) := by
  let k := R.extend P (P.desc g h)
  have hf' := guardAt_parameterOf G k hf
  have hg' : G.guardedAt (R.obj (P.sum A B)) (Y := A) (Z := B) (g ≫ R.out (P.sum A B)) := hg
  have h' := guardAt_compose G (R.obj (P.sum A B)) (h ≫ R.out (P.sum A B)) hf' hg'
  have e : (f ≫ k) ≫ R.out (P.sum A B) =
      ((f ≫ R.out (P.sum Y Z)) ≫ (M.parameter (P.sum Y Z)).map k) ≫
        M.extend (W := R.obj (P.sum A B))
          (P.desc (g ≫ R.out (P.sum A B)) (h ≫ R.out (P.sum A B))) := by
    rw [Category.assoc, show k ≫ R.out (P.sum A B) = _ from R.extend_spec P (P.desc g h),
      P.desc_comp, Category.assoc, Category.assoc]
  exact Eq.mpr (congrArg (G.guardedAt (R.obj (P.sum A B)) (Y := A) (Z := B)) e) h'

theorem observedGuard_trivial {X Y Z : Kleisli (R.monad P)} (f : X ⟶ Y) :
    G.observedGuard R (f ≫ (P.kleisli (R.monad P)).inl (Y := Z)) := by
  have e := comp_pure_of (R.monad P) f (P.inl (Y := Z.of))
  exact Eq.mpr (congrArg (G.ResumptionGuard R (Y := Y.of) (Z := Z.of)) e)
    (resumptionGuard_trivial G R f.of)

theorem observedGuard_parallel {X Y V W : Kleisli (R.monad P)}
    {f : X ⟶ (P.kleisli (R.monad P)).sum V W} {g : Y ⟶ (P.kleisli (R.monad P)).sum V W}
    (hf : G.observedGuard R (Y := V) (Z := W) f)
    (hg : G.observedGuard R (Y := V) (Z := W) g) :
    G.observedGuard R (Y := V) (Z := W) ((P.kleisli (R.monad P)).desc f g) := by
  have e := kleisli_desc_of P (R.monad P) f g
  exact Eq.mpr (congrArg (G.ResumptionGuard R (Y := V.of) (Z := W.of)) e)
    (resumptionGuard_parallel G R hf hg)

theorem observedGuard_compose {X Y Z V W : Kleisli (R.monad P)}
    {f : X ⟶ (P.kleisli (R.monad P)).sum Y Z} {g : Y ⟶ (P.kleisli (R.monad P)).sum V W}
    (h : Z ⟶ (P.kleisli (R.monad P)).sum V W)
    (hf : G.observedGuard R (Y := Y) (Z := Z) f) (hg : G.observedGuard R (Y := V) (Z := W) g) :
    G.observedGuard R (Y := V) (Z := W) (f ≫ (P.kleisli (R.monad P)).desc g h) := by
  let k := (P.kleisli (R.monad P)).desc g h
  have e₁ := R.monad_extend P (X := P.sum Y.of Z.of) (Y := P.sum V.of W.of) k.of
  have e₂ := congrArg (R.extend P (X := P.sum Y.of Z.of) (Y := P.sum V.of W.of))
    (kleisli_desc_of P (R.monad P) g h)
  have e : (f ≫ k).of = f.of ≫ R.extend P (P.desc g.of h.of) :=
    congrArg (fun j => f.of ≫ j) (e₁.trans e₂)
  exact Eq.mpr (congrArg (G.ResumptionGuard R (Y := V.of) (Z := W.of)) e)
    (resumptionGuard_compose G R h.of hf hg)

end Guard

variable (M : ParametrizedGuardedElgotMonad P)

theorem guardAt_parameter {W V X Y Z : C} (k : W ⟶ V)
    {f : X ⟶ (M.obj W).monad.obj (P.sum Y Z)} (hf : M.guardedAt W (Y := Y) (Z := Z) f) :
    M.guardedAt V (Y := Y) (Z := Z) (f ≫ (M.toParametrizedMonad.parameter (P.sum Y Z)).map k) :=
  guardAt_parameterOf M.toGuards k hf

private theorem guardAt_uniform (W : C) {X Y Z : C}
    (f : X ⟶ (M.obj W).monad.obj (P.sum Y X)) (g : Z ⟶ (M.obj W).monad.obj (P.sum Y Z))
    (h : Z ⟶ X) (hf : M.guardedAt W (Y := Y) (Z := X) f)
    (hg : M.guardedAt W (Y := Y) (Z := Z) g)
    (comm : h ≫ f = g ≫ (M.obj W).monad.map (P.map (𝟙 Y) h)) :
    h ≫ ((M.obj W).iteration.iterate (kleisliArrow f) hf).of =
      ((M.obj W).iteration.iterate (kleisliArrow g) hg).of := by
  let T := (M.obj W).monad
  let J := Kleisli.Adjunction.toKleisli T
  let p : J.obj X ⟶ (P.kleisli T).sum (J.obj Y) (J.obj X) := kleisliArrow f
  let q : J.obj Z ⟶ (P.kleisli T).sum (J.obj Y) (J.obj Z) := kleisliArrow g
  have hs : J.map h ≫ p = q ≫ (P.kleisli T).map (𝟙 (J.obj Y)) (J.map h) := by
    rw [← J.map_id, kleisli_map_pure]
    apply Kleisli.hom_ext
    exact (pure_comp_of T h p).trans (comm.trans (comp_pure_of T q (P.map (𝟙 Y) h)).symm)
  have hu := (M.obj W).uniformity p q h hf hg hs
  exact (pure_comp_of T h ((M.obj W).iteration.iterate p hf)).symm.trans
    (congrArg Kleisli.Hom.of hu)

variable (R : FinalResumptions M.toParametrizedMonad)

@[reassoc]
theorem map_out {X Y : C} (g : X ⟶ Y) :
    (R.monad P).map g ≫ R.out Y =
      R.out X ≫ (M.toParametrizedMonad.parameter X).map ((R.monad P).map g) ≫
        (M.obj (R.obj Y)).monad.map g :=
  map_outOf R P g

private theorem diamond_fixpoint {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    f ≫ R.out (P.sum Y X) ≫
      M.toParametrizedMonad.extend (W := R.obj (P.sum Y X))
        (P.desc ((M.obj (R.obj (P.sum Y X))).monad.η.app Y) (M.diamond R f hf)) =
      M.diamond R f hf := by
  let W := R.obj (P.sum Y X)
  let T := (M.obj W).monad
  let kf : Kleisli.mk T X ⟶ Kleisli.mk T (P.sum Y X) := kleisliArrow (f ≫ R.out (P.sum Y X))
  let d : Kleisli.mk T X ⟶ Kleisli.mk T Y := (M.obj W).iteration.iterate kf hf
  let c := (P.kleisli T).desc (𝟙 (Kleisli.mk T Y)) d
  have e : (kf ≫ c).of = d.of :=
    congrArg Kleisli.Hom.of ((M.obj W).iteration.fixpoint kf hf)
  change (f ≫ R.out (P.sum Y X)) ≫ M.toParametrizedMonad.extend (W := W) c.of = _ at e
  rw [show c.of = P.desc (T.η.app Y) d.of from
    kleisli_desc_of P T (𝟙 (Kleisli.mk T Y)) d] at e
  exact (Category.assoc _ _ _).symm.trans e

theorem iterateResumption_fixpoint {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    f ≫ R.extend P (P.desc (R.unit Y) (M.iterateResumption R f hf)) =
      M.iterateResumption R f hf := by
  let W := R.obj (P.sum Y X)
  let d := M.diamond R f hf
  let g := M.iterateResumption R f hf
  let k := R.extend P (P.desc (R.unit Y) g)
  have hg : g ≫ R.out Y = d ≫ (M.toParametrizedMonad.parameter Y).map k := R.solve_spec P d
  have copair : P.desc (R.unit Y) g ≫ R.out Y =
      P.desc ((M.obj W).monad.η.app Y) d ≫ (M.toParametrizedMonad.parameter Y).map k := by
    rw [P.desc_comp, P.desc_comp, hg, R.unit_out]
    exact congrArg (fun j => P.desc j (d ≫ (M.toParametrizedMonad.parameter Y).map k))
      ((M.map k).hom.app_η Y).symm
  have e : (f ≫ k) ≫ R.out Y = g ≫ R.out Y := by
    have extension : k ≫ R.out Y = R.out (P.sum Y X) ≫
        (M.toParametrizedMonad.parameter (P.sum Y X)).map k ≫
          M.toParametrizedMonad.extend (W := R.obj Y) (P.desc (R.unit Y) g ≫ R.out Y) :=
      R.extend_spec P (P.desc (R.unit Y) g)
    have pe := M.toParametrizedMonad.parameter_extend (X := P.sum Y X) (Y := Y) k
      (P.desc ((M.obj W).monad.η.app Y) d)
    have fix : f ≫ R.out (P.sum Y X) ≫
        M.toParametrizedMonad.extend (W := W) (P.desc ((M.obj W).monad.η.app Y) d) = d :=
      diamond_fixpoint M R f hf
    calc
      (f ≫ k) ≫ R.out Y = (f ≫ R.out (P.sum Y X) ≫
          M.toParametrizedMonad.extend (W := W) (P.desc ((M.obj W).monad.η.app Y) d)) ≫
          (M.toParametrizedMonad.parameter Y).map k := by
        simp only [Category.assoc, extension, copair, pe]
      _ = _ := by rw [fix, hg]
  simpa using congrArg (fun j => j ≫ R.roll Y) e

theorem iterateResumption_uniform {X Y Z : C}
    (f : X ⟶ R.obj (P.sum Y X)) (g : Z ⟶ R.obj (P.sum Y Z)) (h : Z ⟶ X)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f)
    (hg : M.ResumptionGuard R (Y := Y) (Z := Z) g)
    (comm : h ≫ f = g ≫ (R.monad P).map (P.map (𝟙 Y) h)) :
    h ≫ M.iterateResumption R f hf = M.iterateResumption R g hg := by
  let A := P.sum Y X
  let B := P.sum Y Z
  let j : R.obj B ⟶ R.obj A := (R.monad P).map (P.map (𝟙 Y) h)
  let u := M.iterateResumption R f hf
  let k := R.extend P (P.desc (R.unit Y) u)
  let l := R.extend P (P.desc (R.unit Y) (h ≫ u))
  let d := M.diamond R f hf
  let e := M.diamond R g hg
  let a := f ≫ R.out A
  let b := (g ≫ R.out B) ≫ (M.toParametrizedMonad.parameter B).map j
  have hb : M.guardedAt (R.obj A) (Y := Y) (Z := Z) b := guardAt_parameter M j hg
  have bodyComm : h ≫ a = b ≫ (M.obj (R.obj A)).monad.map (P.map (𝟙 Y) h) := by
    have c : h ≫ f = g ≫ j := comm
    rw [show a = f ≫ R.out A from rfl, ← Category.assoc, c, Category.assoc]
    exact (congrArg (fun i => g ≫ i) (map_out M R (P.map (𝟙 Y) h))).trans
      (by simp only [b, Category.assoc]; rfl)
  have inner : h ≫ d = e ≫ (M.toParametrizedMonad.parameter Y).map j :=
    (guardAt_uniform M (R.obj A) a b h hf hb bodyComm).trans
      ((M.map j).iteration (g ≫ R.out B) hg).symm
  have jkl : j ≫ k = l := by
    change R.extend P (P.map (𝟙 Y) h ≫ R.unit A) ≫ R.extend P (P.desc (R.unit Y) u) = l
    have e : R.unit A ≫ R.extend P (P.desc (R.unit Y) u) = P.desc (R.unit Y) u :=
      R.unit_extend P _
    rw [R.extend_comp, Category.assoc, e, P.map_desc, Category.id_comp]
  apply R.solve_unique P e
  change (h ≫ u) ≫ R.out Y = e ≫ (M.toParametrizedMonad.parameter Y).map l
  have hu : u ≫ R.out Y = d ≫ (M.toParametrizedMonad.parameter Y).map k :=
    R.solve_spec P d
  calc
    (h ≫ u) ≫ R.out Y = (h ≫ d) ≫ (M.toParametrizedMonad.parameter Y).map k := by
      simp only [Category.assoc, hu]
    _ = _ := by
      rw [inner, Category.assoc]
      exact congrArg (fun p => e ≫ p)
        (((M.toParametrizedMonad.parameter Y).map_comp j k).symm.trans
          (congrArg (M.toParametrizedMonad.parameter Y).map jkl))

theorem iterate_congr {K : Type u} [Category.{v} K] {P' : Coproducts K}
    {G : Guardedness P'} (F : G.Fixpoints) {X Y : K}
    {f g : X ⟶ P'.sum Y X} (e : f = g) (hf : G.guarded f) (hg : G.guarded g) :
    F.iterate f hf = F.iterate g hg := by
  subst g
  rfl

private theorem guardAt_naturality (W : C) {X Y Z : C}
    (f : X ⟶ (M.obj W).monad.obj (P.sum Y X)) (g : Y ⟶ (M.obj W).monad.obj Z)
    (hf : M.guardedAt W (Y := Y) (Z := X) f)
    (hg : M.guardedAt W (Y := Z) (Z := X)
      (f ≫ M.toParametrizedMonad.extend (W := W)
        (P.desc (g ≫ (M.obj W).monad.map P.inl)
          (P.inr ≫ (M.obj W).monad.η.app (P.sum Z X))))) :
    ((M.obj W).iteration.iterate (kleisliArrow (f ≫ M.toParametrizedMonad.extend (W := W)
        (P.desc (g ≫ (M.obj W).monad.map P.inl)
          (P.inr ≫ (M.obj W).monad.η.app (P.sum Z X))))) hg).of =
      ((M.obj W).iteration.iterate (kleisliArrow f) hf).of ≫ M.toParametrizedMonad.extend (W := W) g := by
  let T := (M.obj W).monad
  let K := P.kleisli T
  let f' : Kleisli.mk T X ⟶ Kleisli.mk T (P.sum Y X) := kleisliArrow f
  let g' : Kleisli.mk T Y ⟶ Kleisli.mk T Z := kleisliArrow g
  let k := K.map g' (𝟙 (Kleisli.mk T X))
  let c := P.desc (g ≫ T.map (P.inl (Y := X))) (P.inr ≫ T.η.app (P.sum Z X))
  have ek : k.of = c := by
    change (K.desc (g' ≫ K.inl) (𝟙 (Kleisli.mk T X) ≫ K.inr)).of = c
    exact (kleisli_desc_of P T _ _).trans
      (congrArg₂ P.desc (comp_pure_of T g' P.inl)
        (congrArg Kleisli.Hom.of (Category.id_comp (K.inr (X := Kleisli.mk T Z)))))
  have ef : f' ≫ k = kleisliArrow (f ≫ M.toParametrizedMonad.extend (W := W) c) :=
    Kleisli.hom_ext (congrArg (fun j => f ≫ M.toParametrizedMonad.extend (W := W) j) ek)
  have hg' : (M.obj W).guard.guarded (Y := Kleisli.mk T Z) (Z := Kleisli.mk T X) (f' ≫ k) :=
    Eq.mpr (congrArg ((M.obj W).guard.guarded (Y := Kleisli.mk T Z) (Z := Kleisli.mk T X)) ef) hg
  exact congrArg Kleisli.Hom.of
    ((iterate_congr (M.obj W).iteration.toFixpoints ef.symm hg hg').trans
      ((M.obj W).iteration.naturalCodiagonal.naturality f' g' hf hg'))

theorem naturalityBody_guarded {X Y Z : C} (f : X ⟶ R.obj (P.sum Y X)) (g : Y ⟶ R.obj Z)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    M.ResumptionGuard R (Y := Z) (Z := X) (M.naturalityBody R f g) :=
  resumptionGuard_compose M.toGuards R _ hf (resumptionGuard_trivial M.toGuards R g)

theorem iterateResumption_naturality {X Y Z : C} (f : X ⟶ R.obj (P.sum Y X)) (g : Y ⟶ R.obj Z)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f)
    (hg : M.ResumptionGuard R (Y := Z) (Z := X) (M.naturalityBody R f g)) :
    M.iterateResumption R (M.naturalityBody R f g) hg =
      M.iterateResumption R f hf ≫ R.extend P g := by
  let A := P.sum Y X
  let B := P.sum Z X
  let V := R.obj B
  let T := (M.obj V).monad
  let i : Z ⟶ B := P.inl
  let j : X ⟶ B := P.inr
  let m : R.obj Z ⟶ V := (R.monad P).map i
  let h := P.desc (g ≫ m) (j ≫ R.unit B)
  let p := R.extend P h
  let q := R.extend P g
  let F := M.naturalityBody R f g
  let u := M.iterateResumption R f hf
  let d := M.diamond R f hf
  let e := M.diamond R F hg
  let a := (f ≫ R.out A) ≫ (M.toParametrizedMonad.parameter A).map p
  let b := (g ≫ R.out Z) ≫ (M.toParametrizedMonad.parameter Z).map m
  let c := P.desc (b ≫ T.map i) (j ≫ T.η.app B)
  let k := R.extend P (P.desc (R.unit Y) u)
  let l := R.extend P (P.desc (R.unit Z) (u ≫ q))
  let Q := M.toParametrizedMonad

  have ha : M.guardedAt V (Y := Y) (Z := X) a := guardAt_parameter M p hf
  have hc : h ≫ R.out B = c := by
    have first : (g ≫ m) ≫ R.out B = b ≫ T.map i := by
      calc
        _ = g ≫ (m ≫ R.out B) := Category.assoc _ _ _
        _ = _ := (congrArg (fun j => g ≫ j) (map_out M R i)).trans (by simp only [b, T, V, B, m, Category.assoc]; rfl)
    have second : (j ≫ R.unit B) ≫ R.out B = j ≫ T.η.app B :=
      (Category.assoc _ _ _).trans (congrArg (fun z => j ≫ z) (R.unit_out B))
    exact (P.desc_comp _ _ _).trans (congrArg₂ P.desc first second)
  have af : F ≫ R.out B = a ≫ Q.extend (W := V) c := by
    change (f ≫ p) ≫ R.out B = _
    have e' : p ≫ R.out B = R.out A ≫ (Q.parameter A).map p ≫ Q.extend (W := V) (h ≫ R.out B) :=
      R.extend_spec P h
    simp only [a, Category.assoc, e', hc]
    rfl
  have eSpec : e = (d ≫ (Q.parameter Y).map p) ≫ Q.extend (W := V) b := by
    have hb : M.guardedAt V (Y := Z) (Z := X) (a ≫ Q.extend (W := V) c) :=
      Eq.mp (congrArg (M.guardedAt V (Y := Z) (Z := X)) af) hg
    have e' : e =
        ((M.obj V).iteration.iterate (kleisliArrow (a ≫ Q.extend (W := V) c)) hb).of :=
      congrArg Kleisli.Hom.of
        (iterate_congr (M.obj V).iteration.toFixpoints (congrArg (fun z => kleisliArrow z) af) hg hb)
    have d' : d ≫ (Q.parameter Y).map p =
        ((M.obj V).iteration.iterate (kleisliArrow a) ha).of :=
      (M.map p).iteration (f ≫ R.out A) hf
    exact e'.trans ((guardAt_naturality M V a b ha hb).trans (congrArg (fun z => z ≫ Q.extend (W := V) b) d'.symm))

  have ml : m ≫ l = 𝟙 (R.obj Z) := by
    change R.extend P (i ≫ R.unit B) ≫ R.extend P (P.desc (R.unit Z) (u ≫ q)) = _
    have e' : R.unit B ≫ R.extend P (P.desc (R.unit Z) (u ≫ q)) = P.desc (R.unit Z) (u ≫ q) :=
      R.unit_extend P _
    rw [R.extend_comp, Category.assoc, e', P.inl_desc, R.extend_unit]
  have kl : k ≫ q = p ≫ l := by
    change R.extend P (P.desc (R.unit Y) u) ≫ q = R.extend P h ≫ l
    have ju : (j ≫ R.unit B) ≫ l = u ≫ q := by
      calc
        _ = j ≫ P.desc (R.unit Z) (u ≫ q) :=
          (Category.assoc _ _ _).trans (congrArg (fun z => j ≫ z) (R.unit_extend P _))
        _ = _ := P.inr_desc _ _
    have gml : (g ≫ m) ≫ l = g :=
      (Category.assoc _ _ _).trans ((congrArg (fun z => g ≫ z) ml).trans (Category.comp_id _))
    rw [R.extend_comp, R.extend_comp, P.desc_comp, P.desc_comp]
    exact congrArg (R.extend P)
      (congrArg₂ P.desc ((R.unit_extend P g).trans gml.symm) ju.symm)

  symm
  apply R.solve_unique P e
  change (u ≫ q) ≫ R.out Z = e ≫ (Q.parameter Z).map l
  have eu : u ≫ R.out Y = d ≫ (Q.parameter Y).map k := R.solve_spec P d
  have eq : q ≫ R.out Z = R.out Y ≫ (Q.parameter Y).map q ≫
      Q.extend (W := R.obj Z) (g ≫ R.out Z) := R.extend_spec P g
  have bl : b ≫ (Q.parameter Z).map l = g ≫ R.out Z := by
    calc
      _ = (g ≫ R.out Z) ≫ (Q.parameter Z).map (m ≫ l) := by rw [Functor.map_comp, Category.assoc]
      _ = _ := by rw [ml, Functor.map_id, Category.comp_id]
  calc
    (u ≫ q) ≫ R.out Z = d ≫ (Q.parameter Y).map (k ≫ q) ≫
        Q.extend (W := R.obj Z) (g ≫ R.out Z) := by
      rw [Category.assoc, eq, ← Category.assoc, eu, Functor.map_comp]
      simp only [Category.assoc]
    _ = ((d ≫ (Q.parameter Y).map p) ≫ Q.extend (W := V) b) ≫ (Q.parameter Z).map l := by
      have pe := Q.parameter_extend (X := Y) (Y := Z) l b
      rw [kl, Functor.map_comp, ← bl]
      simp only [Category.assoc, pe]
    _ = _ := by rw [eSpec]

theorem resumption_comp_of {X Y Z : Kleisli (R.monad P)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).of = f.of ≫ R.extend P g.of :=
  congrArg (fun z => f.of ≫ z) (R.monad_extend P g.of)

theorem observedFixpoint {X Y : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y X)
    (hf : M.observedGuard R (Y := Y) (Z := X) f) :
    Guardedness.IsFixpoint f
      (kleisliArrow (M.iterateResumption R f.of hf)) := by
  let q : X ⟶ Y := kleisliArrow (M.iterateResumption R f.of hf)
  change f ≫ (P.kleisli (R.monad P)).desc (𝟙 Y) q = q
  apply Kleisli.hom_ext
  exact (resumption_comp_of M R f _).trans
    ((congrArg (fun z => f.of ≫ R.extend P z) (kleisli_desc_of P (R.monad P) (𝟙 Y) q)).trans
      (iterateResumption_fixpoint M R f.of hf))

end Silmaril.Calco2019.Proofs
