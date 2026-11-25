module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Interpretation.Multiplication
import Silmaril.Proofs.Semantics.Calco2019.ExceptionResumptionInterpretation
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

section Substitute

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

private theorem codiagonal_substitute (F : G.Fixpoints) (N : F.NaturalCodiagonal)
    {A V Y : K} (f : A ⟶ P.sum V A) (g : V ⟶ P.sum Y A)
    (hf : G.guarded f) (hg : G.guarded g)
    (hflat : G.guarded (f ≫ P.desc g P.inr))
    (hsolved : G.guarded (F.iterate f hf ≫ g)) :
    F.iterate (f ≫ P.desc g P.inr) hflat = F.iterate (F.iterate f hf ≫ g) hsolved := by
  let d := f ≫ P.map g (𝟙 A)
  have eq : d ≫ P.assoc (X := Y) (Y := A) (Z := A) =
      f ≫ P.desc (g ≫ P.map (𝟙 Y) (P.inl (X := A) (Y := A))) (P.inr ≫ P.inr) := by
    simp [d, Coproducts.assoc, Coproducts.map, Category.assoc]
  have hn : G.nested (Y := Y) (Z := A) (W := A) d := by
    change G.guarded (d ≫ P.assoc (X := Y))
    rw [eq]
    exact G.compose _ hf (Guardedness.map hg _ _)
  have hi : G.guarded (Y := P.sum Y A) (Z := A) d := Guardedness.map hf g (𝟙 A)
  have ho := Guardedness.guarded_fixpoint hn (F.fixpoint d hi)
  have dm : d ≫ P.merge = f ≫ P.desc g P.inr := by
    simp [d, Coproducts.merge, Coproducts.map, Category.assoc]
  exact (iterate_congr F dm.symm hflat (Guardedness.merge hn)).trans
    ((N.codiagonal d hn hi ho (Guardedness.merge hn)).trans
      (iterate_congr F (N.naturality f g hf hi) ho hsolved))

end Substitute

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

local notation "Q" => S.monad
local notation "K" => P.kleisli Q
local notation "J" => Kleisli.Adjunction.toKleisli Q

private noncomputable def handle (Y W : C) :
    (K).sum (Kleisli.mk Q Y) (Kleisli.mk Q (H.obj W)) ⟶
      (K).sum (Kleisli.mk Q Y) (Kleisli.mk Q W) :=
  (K).desc (K).inl (kleisliArrow (σ.val.app W) ≫ (K).inr)

private theorem operation_guard (W : C) {V Z : Kleisli Q}
    (k : Kleisli.mk Q W ⟶ (K).sum V Z) :
    S.guard.guarded (Y := V) (Z := Z) (kleisliArrow (σ.val.app W) ≫ k) := by
  let s := kleisliArrow (σ.val.app W)
  exact post_guarded s k (Kleisli.hom_ext (comp_pure_of Q s P.inr) ▸ σ.property W)

omit [HasInitial C] in
private theorem inl_guard (Y W : Kleisli Q) :
    S.guard.guarded (Y := Y) (Z := W) ((K).inl (X := Y) (Y := W)) := by
  simpa only [Category.id_comp] using S.guard.trivial (Z := W) (𝟙 Y)

private theorem handle_natural (Y : C) {U V : C} (q : U ⟶ V) :
    (K).map (𝟙 (Kleisli.mk Q Y)) ((J).map (H.map q)) ≫ handle σ Y V =
      handle σ Y U ≫ (K).map (𝟙 (Kleisli.mk Q Y)) ((J).map q) := by
  have n : (J).map (H.map q) ≫ kleisliArrow (σ.val.app V) =
      kleisliArrow (σ.val.app U) ≫ (J).map q :=
    Kleisli.hom_ext ((pure_comp_of Q _ _).trans
      ((σ.val.naturality q).trans (comp_pure_of Q _ _).symm))
  refine (K).hom_ext (X := Kleisli.mk Q Y) (Y := Kleisli.mk Q (H.obj U)) ?_ ?_
  · simp [handle, Coproducts.map, Category.assoc]
  · simp [handle, Coproducts.map, Category.assoc, ← reassoc_of% n]

private theorem unit_body (Y : C) :
    (J).map (R.unit Y) ≫ mediatorBody R ξ σ Y =
      (K).inl (X := Kleisli.mk Q Y) (Y := Kleisli.mk Q (R.obj Y)) := by
  let A := P.sum Y (H.obj (R.obj Y))
  let obs : Kleisli.mk Q (R.obj Y) ⟶ Kleisli.mk Q A :=
    kleisliArrow (R.out Y ≫ ξ.hom.app A)
  have e : (J).map (R.unit Y) ≫ obs =
      (K).inl (X := Kleisli.mk Q Y) (Y := Kleisli.mk Q (H.obj (R.obj Y))) := by
    apply Kleisli.hom_ext
    rw [pure_comp_of Q, ← Category.assoc]
    change (R.unit Y ≫ R.out Y) ≫ ξ.hom.app A = P.inl ≫ (Q).η.app A
    have h : R.unit Y ≫ R.out Y = P.inl ≫ T.monad.η.app A := R.unit_out Y
    rw [h, Category.assoc, ξ.hom.app_η]
  change (J).map (R.unit Y) ≫ obs ≫ handle σ Y (R.obj Y) = _
  rw [← Category.assoc, e]
  exact (K).inl_desc _ _

private theorem observation_body {X Y W : C} (d : X ⟶ T.monad.obj (P.sum Y (H.obj W)))
    (g : X ⟶ R.obj Y) (q : W ⟶ R.obj Y)
    (h : g ≫ R.out Y = d ≫ T.monad.map (P.map (𝟙 Y) (H.map q))) :
    (J).map g ≫ mediatorBody R ξ σ Y =
      (kleisliArrow (d ≫ ξ.hom.app (P.sum Y (H.obj W))) ≫ handle σ Y W) ≫
        (K).map (𝟙 (Kleisli.mk Q Y)) ((J).map q) := by
  let A := P.sum Y (H.obj W)
  let B := P.sum Y (H.obj (R.obj Y))
  let j := P.map (𝟙 Y) (H.map q)
  let obs : Kleisli.mk Q (R.obj Y) ⟶ Kleisli.mk Q B :=
    kleisliArrow (R.out Y ≫ ξ.hom.app B)
  let obs' : Kleisli.mk Q X ⟶ Kleisli.mk Q A := kleisliArrow (d ≫ ξ.hom.app A)
  have e : (J).map g ≫ obs = obs' ≫ (K).map (𝟙 (Kleisli.mk Q Y)) ((J).map (H.map q)) := by
    have hid : 𝟙 (Kleisli.mk Q Y) = (J).map (𝟙 Y) := ((J).map_id Y).symm
    rw [hid, kleisli_map_pure]
    apply Kleisli.hom_ext
    rw [pure_comp_of Q, comp_pure_of Q]
    change g ≫ R.out Y ≫ ξ.hom.app B = (d ≫ ξ.hom.app A) ≫ (Q).map j
    rw [← Category.assoc, h, Category.assoc, ξ.hom.toNatTrans.naturality, Category.assoc]
  change (J).map g ≫ obs ≫ handle σ Y (R.obj Y) = _
  rw [← Category.assoc, e, Category.assoc, handle_natural σ Y q, Category.assoc]


theorem mediator_iterate {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : (parametrizedElgot T H).ResumptionGuard R (Y := Y) (Z := X) f) :
    (J).map ((parametrizedElgot T H).iterateResumption R f hf) ≫ Exception.mediator R ξ σ Y =
      S.iteration.iterate ((J).map f ≫ Exception.mediator R ξ σ (P.sum Y X))
        (mediator_guard R ξ σ f hf) := by
  let M := parametrizedElgot T H
  let F := S.iteration.toFixpoints
  let N := S.iteration.naturalCodiagonal
  let k := (K)
  let Z := P.sum Y X
  let W := R.obj Z
  let E := H.obj W
  let x := Kleisli.mk Q X
  let y := Kleisli.mk Q Y
  let w := Kleisli.mk Q W
  let u : X ⟶ T.monad.obj (P.sum (P.sum Y E) X) := (f ≫ R.out Z) ≫ T.monad.map (rearrange P E)
  let d : X ⟶ T.monad.obj (P.sum Y E) := M.diamond R f hf
  let g := M.iterateResumption R f hf
  let p : Z ⟶ R.obj Y := P.desc (R.unit Y) g
  let q := R.extend P p
  let jq := (J).map q
  let m := Exception.mediator R ξ σ Z
  let s : Kleisli.mk Q E ⟶ w := kleisliArrow (σ.val.app W)
  let c := handle σ Y W
  let c' := k.desc (k.inl (X := y) (Y := x)) (s ≫ m)
  let v : x ⟶ k.sum (k.sum y (Kleisli.mk Q E)) x :=
    kleisliArrow (u ≫ ξ.hom.app (P.sum (P.sum Y E) X))
  let b : x ⟶ k.sum y w := kleisliArrow (d ≫ ξ.hom.app (P.sum Y E)) ≫ c
  have hv : S.guard.guarded (Y := k.sum y (Kleisli.mk Q E)) (Z := x) v := ξ.guarded u hf
  have hc' : S.guard.guarded (Y := y) (Z := x) c' :=
    S.guard.parallel (inl_guard y x) (operation_guard σ W m)
  have hc : S.guard.guarded (Y := y) (Z := w) c :=
    S.guard.parallel (inl_guard y w) (operation_guard σ W k.inr)
  have hb : S.guard.guarded (Y := y) (Z := w) b :=
    Guardedness.precomp hc (kleisliArrow (d ≫ ξ.hom.app (P.sum Y E)))
  let a := mediatorBody R ξ σ Z
  have ha := mediatorBody_guarded R ξ σ Z
  let l := k.desc (k.inl (X := y) (Y := w)) b
  have hl : S.guard.guarded (Y := y) (Z := w) l :=
    S.guard.parallel (inl_guard y w) hb
  let t := a ≫ k.desc l (k.inr (X := y) (Y := w))
  have ht : S.guard.guarded (Y := y) (Z := w) t := S.guard.compose _ ha hl
  obtain ⟨hleft, hright⟩ := Guardedness.dinaturality_bodies m b (Or.inr hb)
  let r := b ≫ k.desc (k.inl (X := y) (Y := x)) m
  have right_eq : F.iterate (v ≫ k.desc c' (k.inr (X := y) (Y := x)))
      (S.guard.compose _ hv hc') = F.iterate r hright := by
    have de : kleisliArrow (d ≫ ξ.hom.app (P.sum Y E)) = F.iterate v hv :=
      Kleisli.hom_ext (ξ.iteration u hf)
    have eq : F.iterate v hv ≫ c' = r := by
      rw [← de]
      have e : c ≫ k.desc (k.inl (X := y) (Y := x)) m = c' := by
        change k.desc (k.inl (X := y) (Y := w)) (s ≫ k.inr) ≫ k.desc k.inl m = _
        simp only [c', Coproducts.desc_comp, Category.assoc, Coproducts.inl_desc, Coproducts.inr_desc]
      change _ = (_ ≫ c) ≫ k.desc k.inl m
      rw [Category.assoc, e]
    exact (codiagonal_substitute F N v c' hv hc' _ (Guardedness.precomp hc' _)).trans
      (iterate_congr F eq (Guardedness.precomp hc' _) hright)
  have left_eq : F.iterate t ht = m ≫ k.desc (𝟙 y) (F.iterate r hright) :=
    (codiagonal_substitute F N a l ha hl ht hleft).trans
      (S.iteration.dinaturality m b (Or.inr hb) hleft hright)
  let mapq := k.map (𝟙 y) jq
  let body := mediatorBody R ξ σ Y
  have g_out : g ≫ R.out Y = d ≫ T.monad.map (P.map (𝟙 Y) (H.map q)) :=
    (M.iterateResumption_characterization R f hf).1
  have g_body : (J).map g ≫ body = b ≫ mapq := observation_body R ξ σ d g q g_out
  have pbody : (J).map p ≫ body = k.desc (k.inl (X := y) (Y := Kleisli.mk Q (R.obj Y))) (b ≫ mapq) := by
    refine k.hom_ext (X := y) (Y := x) ?_ ?_
    · rw [← Category.assoc]
      change ((J).map (P.inl (X := Y) (Y := X)) ≫ (J).map p) ≫ body = _
      rw [← (J).map_comp, show P.inl ≫ p = R.unit Y from P.inl_desc _ _]
      exact (unit_body R ξ σ Y).trans (k.inl_desc _ _).symm
    · rw [← Category.assoc]
      change ((J).map (P.inr (X := Y) (Y := X)) ≫ (J).map p) ≫ body = _
      rw [← (J).map_comp, show P.inr ≫ p = g from P.inr_desc _ _]
      exact g_body.trans (k.inr_desc _ _).symm
  have uniform : jq ≫ body = t ≫ mapq := by
    have eq := Exception.mediatorBody_extend R ξ σ p
    change jq ≫ body = a ≫ k.desc ((J).map p ≫ body) (jq ≫ k.inr) at eq
    rw [eq, pbody]
    change _ = (a ≫ k.desc (k.desc k.inl b) k.inr) ≫ mapq
    simp [mapq, k, Coproducts.map, Category.assoc]
  have q_solution : jq ≫ Exception.mediator R ξ σ Y = F.iterate t ht :=
    S.uniformity body t q (mediatorBody_guarded R ξ σ Y) ht uniform
  let j : X ⟶ W := P.inr ≫ R.unit Z
  have jq_eq : j ≫ q = g := by
    change (P.inr ≫ R.unit Z) ≫ R.extend P p = g
    rw [Category.assoc, R.unit_extend, show P.inr ≫ p = g from P.inr_desc _ _]
  have jm : (J).map j ≫ m = k.inr (X := y) (Y := x) := by
    change (J).map (P.inr ≫ R.unit Z) ≫ Exception.mediator R ξ σ Z = _
    rw [(J).map_comp, Category.assoc, Exception.mediator_unit R ξ σ Z]
    exact Category.comp_id (k.inr (X := y) (Y := x))
  calc
    (J).map g ≫ Exception.mediator R ξ σ Y = (J).map j ≫ F.iterate t ht := by
      rw [← jq_eq, (J).map_comp, Category.assoc]
      exact congrArg ((J).map j ≫ ·) q_solution
    _ = F.iterate r hright := by
      rw [left_eq, ← Category.assoc, jm, Coproducts.inr_desc]
    _ = _ := by
      have e : (J).map f ≫ Exception.mediator R ξ σ Z = v ≫ k.desc c' (k.inr (X := y) (Y := x)) :=
        normalized_mediator R ξ σ f
      exact right_eq.symm.trans
        (iterate_congr F e.symm (S.guard.compose _ hv hc') (mediator_guard R ξ σ f hf))


theorem mediator_monad_guard :
    MonadGuardedness.Preserves P ((parametrizedElgot T H).resumptionElgotMonad R).guard
      S.guard (mediatorMonadHom R ξ σ) := by
  intro X Y Z f hf
  let M := parametrizedElgot T H
  have h := (M.resumptionGuardedness_iff R
    (Y := Kleisli.mk (R.monad P) Y) (Z := Kleisli.mk (R.monad P) Z)
    (kleisliArrow f)).mp hf
  have e := Kleisli.hom_ext (pure_comp_of Q f (Exception.mediator R ξ σ (P.sum Y Z)))
  rw [mediatorMonadHom_app]
  exact Eq.mp (congrArg (S.guard.guarded (Y := Kleisli.mk Q Y) (Z := Kleisli.mk Q Z)) e)
    (Exception.mediator_guard R ξ σ f h)

theorem mediator_iterate_of {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : ((parametrizedElgot T H).resumptionElgotMonad R).guard.guarded
      (Y := Kleisli.mk (R.monad P) Y) (Z := Kleisli.mk (R.monad P) X) (kleisliArrow f)) :
    (((parametrizedElgot T H).resumptionElgotMonad R).iteration.iterate
      (kleisliArrow f) hf).of ≫ (mediatorMonadHom R ξ σ).app Y =
      (S.iteration.iterate (kleisliArrow (f ≫ (mediatorMonadHom R ξ σ).app (P.sum Y X)))
        (mediator_monad_guard R ξ σ f hf)).of := by
  let M := parametrizedElgot T H
  have h := (M.resumptionGuardedness_iff R (Y := Kleisli.mk (R.monad P) Y)
    (Z := Kleisli.mk (R.monad P) X) (kleisliArrow f)).mp hf
  let g := M.iterateResumption R f h
  have e := mediator_iterate R ξ σ f h
  have he : (J).map f ≫ Exception.mediator R ξ σ (P.sum Y X) =
      kleisliArrow (f ≫ (mediatorMonadHom R ξ σ).app (P.sum Y X)) := by
    rw [mediatorMonadHom_app]
    exact Kleisli.hom_ext (pure_comp_of Q _ _)
  rw [mediatorMonadHom_app]
  exact (pure_comp_of Q g _).symm.trans
    (congrArg Kleisli.Hom.of (e.trans (iterate_congr S.iteration.toFixpoints he
      (Exception.mediator_guard R ξ σ f h) (mediator_monad_guard R ξ σ f hf))))

end Silmaril.Calco2019.Proofs
