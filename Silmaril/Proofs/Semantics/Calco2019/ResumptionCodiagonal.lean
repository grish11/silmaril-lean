module

public import Silmaril.Semantics.Calco2019.ResumptionGuardThms
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

private theorem kleisli_desc_pure (T : CategoryTheory.Monad C) {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (P.kleisli T).desc ((Kleisli.Adjunction.toKleisli T).map f) ((Kleisli.Adjunction.toKleisli T).map g) =
      (Kleisli.Adjunction.toKleisli T).map (P.desc f g) :=
  Kleisli.hom_ext ((kleisli_desc_of P T _ _).trans (P.desc_comp f g (T.η.app Z)).symm)

theorem kleisli_assoc_pure (T : CategoryTheory.Monad C) (X Y Z : C) :
    (P.kleisli T).assoc (X := Kleisli.mk T X) (Y := Kleisli.mk T Y) (Z := Kleisli.mk T Z) =
      (Kleisli.Adjunction.toKleisli T).map (P.assoc (X := X) (Y := Y) (Z := Z)) := by
  let J := Kleisli.Adjunction.toKleisli T
  let K := P.kleisli T
  change K.desc (K.desc (J.map P.inl) (J.map P.inl ≫ J.map P.inr)) (J.map P.inr ≫ J.map P.inr) =
    J.map (P.desc (P.desc P.inl (P.inl ≫ P.inr)) (P.inr ≫ P.inr))
  rw [← J.map_comp, ← J.map_comp, kleisli_desc_pure]
  exact kleisli_desc_pure T _ _

theorem kleisli_merge_pure (T : CategoryTheory.Monad C) (X Y : C) :
    (P.kleisli T).merge (X := Kleisli.mk T X) (Y := Kleisli.mk T Y) =
      (Kleisli.Adjunction.toKleisli T).map (P.merge (X := X) (Y := Y)) := by
  let J := Kleisli.Adjunction.toKleisli T
  change (P.kleisli T).desc (𝟙 (J.obj (P.sum Y X))) (J.map P.inr) = J.map (P.desc (𝟙 (P.sum Y X)) P.inr)
  rw [← J.map_id, kleisli_desc_pure]

variable (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)

private theorem post_out {S A B : C} (f : S ⟶ R.obj A) (j : A ⟶ B) :
    (f ≫ (R.monad P).map j) ≫ R.out B = (f ≫ R.out A ≫ (M.obj (R.obj A)).monad.map j) ≫
      (M.toParametrizedMonad.parameter B).map ((R.monad P).map j) := by
  have e := congrArg (fun k => f ≫ k) (map_out M R j)
  calc
    _ = f ≫ ((R.monad P).map j ≫ R.out B) := Category.assoc _ _ _
    _ = _ := by
      apply e.trans
      simp only [Category.assoc]
      exact congrArg (fun k => f ≫ R.out A ≫ k)
        ((M.map ((R.monad P).map j)).hom.toNatTrans.naturality j).symm

private theorem nestedObservation {S X Y Z : C} (f : S ⟶ R.obj (P.sum (P.sum X Y) Z))
    (hf : M.ResumptionNested R (X := X) (Y := Y) (Z := Z) f) :
    (M.obj (R.obj (P.sum (P.sum X Y) Z))).guard.nested
      (Y := Kleisli.mk _ X) (Z := Kleisli.mk _ Y) (W := Kleisli.mk _ Z)
      (kleisliArrow (f ≫ R.out (P.sum (P.sum X Y) Z))) := by
  let A := P.sum (P.sum X Y) Z
  let B := P.sum X (P.sum Y Z)
  let a : A ⟶ B := P.assoc
  let i : R.obj A ⟶ R.obj B := (R.monad P).map a
  let j : R.obj B ⟶ R.obj A := (R.monad P).map P.assocInv
  let Q := M.toParametrizedMonad
  let b := f ≫ R.out A ≫ (M.obj (R.obj A)).monad.map a
  have he : (f ≫ i) ≫ R.out B = b ≫ (Q.parameter B).map i := post_out M R f a
  have h' : M.guardedAt (R.obj B) (Y := X) (Z := P.sum Y Z) (b ≫ (Q.parameter B).map i) :=
    Eq.mp (congrArg (M.guardedAt (R.obj B) (Y := X) (Z := P.sum Y Z)) he) hf
  have hj : i ≫ j = 𝟙 (R.obj A) := by
    exact (((R.functor P).map_comp a P.assocInv).symm.trans
      ((congrArg (R.functor P).map (P.assoc_assocInv X Y Z)).trans ((R.functor P).map_id A)))
  have cancel : (Q.parameter B).map i ≫ (Q.parameter B).map j = 𝟙 ((M.obj (R.obj A)).monad.obj B) :=
    (((Q.parameter B).map_comp i j).symm.trans
      ((congrArg (Q.parameter B).map hj).trans ((Q.parameter B).map_id (R.obj A))))
  have guard := guardAt_parameter M j h'
  have e : (b ≫ (Q.parameter B).map i) ≫ (Q.parameter B).map j = b := by
    rw [Category.assoc, cancel, Category.comp_id]
  have hb := Eq.mp (congrArg (M.guardedAt (R.obj A) (Y := X) (Z := P.sum Y Z)) e) guard
  let T := (M.obj (R.obj A)).monad
  let k : Kleisli.mk T S ⟶ Kleisli.mk T A := kleisliArrow (f ≫ R.out A)
  have ek : (k ≫ (P.kleisli T).assoc).of = b := by
    rw [kleisli_assoc_pure]
    exact (comp_pure_of T k a).trans (Category.assoc _ _ _)
  exact Eq.mpr (congrArg ((M.obj (R.obj A)).guard.guarded
    (Y := Kleisli.mk T X) (Z := Kleisli.mk T (P.sum Y Z))) (Kleisli.hom_ext ek)) hb

private theorem mergeObservation {S X Y W : C}
    (f : S ⟶ (M.obj W).monad.obj (P.sum (P.sum Y X) X)) :
    (kleisliArrow f ≫ (P.kleisli (M.obj W).monad).merge).of = f ≫ (M.obj W).monad.map P.merge := by
  rw [kleisli_merge_pure]
  exact comp_pure_of _ _ _

theorem iterateResumption_codiagonal {X Y : C}
    (f : X ⟶ R.obj (P.sum (P.sum Y X) X))
    (hf : M.ResumptionNested R (X := Y) (Y := X) (Z := X) f) :
    ∃ (h₁ : M.ResumptionGuard R (Y := P.sum Y X) (Z := X) f)
      (h₂ : M.ResumptionGuard R (Y := Y) (Z := X) (M.iterateResumption R f h₁))
      (hm : M.ResumptionGuard R (Y := Y) (Z := X) (f ≫ (R.monad P).map P.merge)),
      M.iterateResumption R (f ≫ (R.monad P).map P.merge) hm =
        M.iterateResumption R (M.iterateResumption R f h₁) h₂ := by
  let A := P.sum Y X
  let B := P.sum A X
  let W := R.obj B
  let V := R.obj A
  let T := (M.obj W).monad
  let I := (M.obj W).iteration
  let Q := M.toParametrizedMonad
  let a := f ≫ R.out B
  let b := a ≫ T.map (P.merge (X := X) (Y := Y))
  let p : Kleisli.mk T X ⟶ Kleisli.mk T B := kleisliArrow a
  let s := p ≫ (P.kleisli T).merge
  have hn : (M.obj W).guard.nested
      (Y := Kleisli.mk T Y) (Z := Kleisli.mk T X) (W := Kleisli.mk T X) p :=
    nestedObservation M R f hf
  have h₁ : M.ResumptionGuard R (Y := A) (Z := X) f := Guardedness.weaken hn
  have hNestedOuter := Guardedness.guarded_fixpoint hn (I.fixpoint p h₁)
  have hflat := Guardedness.merge hn
  have es : s.of = b := mergeObservation M a
  have hb : M.guardedAt W (Y := Y) (Z := X) b :=
    Eq.mp (congrArg ((M.obj W).guard.guarded (Y := Kleisli.mk T Y) (Z := Kleisli.mk T X))
      (Kleisli.hom_ext es)) hflat
  let d := M.diamond R f h₁
  let D := (I.iterate (I.iterate p h₁) hNestedOuter).of
  have baseDouble : (I.iterate (kleisliArrow b) hb).of = D :=
    congrArg Kleisli.Hom.of
      ((iterate_congr I.toFixpoints (Kleisli.hom_ext es).symm hb hflat).trans
        (I.naturalCodiagonal.codiagonal p hn h₁ hNestedOuter hflat))
  let u := M.iterateResumption R f h₁
  let k := R.extend P (P.desc (R.unit A) u)
  have eu : u ≫ R.out A = d ≫ (Q.parameter A).map k := R.solve_spec P d
  have hk := guardAt_parameter M k hNestedOuter
  have h₂ : M.ResumptionGuard R (Y := Y) (Z := X) u :=
    Eq.mpr (congrArg (M.guardedAt V (Y := Y) (Z := X)) eu) hk
  let v := M.iterateResumption R u h₂
  let l := R.extend P (P.desc (R.unit Y) v)
  let e := M.diamond R u h₂
  have ed : e = D ≫ (Q.parameter Y).map k :=
    (congrArg Kleisli.Hom.of
      (iterate_congr (M.obj V).iteration.toFixpoints (congrArg (fun z => kleisliArrow z) eu) h₂ hk)).trans
      ((M.map k).iteration d hNestedOuter).symm
  let m : W ⟶ V := (R.monad P).map P.merge
  have em : (f ≫ m) ≫ R.out A = b ≫ (Q.parameter A).map m :=
    (post_out M R f P.merge).trans
      (congrArg (fun z => z ≫ (Q.parameter A).map m) (Category.assoc _ _ _).symm)
  have hm' := guardAt_parameter M m hb
  have hm : M.ResumptionGuard R (Y := Y) (Z := X) (f ≫ m) :=
    Eq.mpr (congrArg (M.guardedAt V (Y := Y) (Z := X)) em) hm'
  let df := M.diamond R (f ≫ m) hm
  have eDf : df = D ≫ (Q.parameter Y).map m := by
    refine (congrArg Kleisli.Hom.of
      (iterate_congr (M.obj V).iteration.toFixpoints (congrArg (fun z => kleisliArrow z) em) hm hm')).trans ?_
    exact ((M.map m).iteration b hb).symm.trans
      (congrArg (fun z => z ≫ (Q.parameter Y).map m) baseDouble)
  have ekl : k ≫ l = m ≫ l := by
    change R.extend P (P.desc (R.unit A) u) ≫ l =
      R.extend P (P.merge ≫ R.unit A) ≫ l
    have el : R.unit A ≫ l = P.desc (R.unit Y) v := R.unit_extend P _
    have ev : u ≫ l = v := iterateResumption_fixpoint M R u h₂
    rw [R.extend_comp, R.extend_comp, P.desc_comp, Category.assoc, el, ev]
    simp [Coproducts.merge]
  refine ⟨h₁, h₂, hm, ?_⟩
  symm
  apply R.solve_unique P df
  change v ≫ R.out Y = df ≫ (Q.parameter Y).map l
  have vSpec : v ≫ R.out Y = e ≫ (Q.parameter Y).map l := R.solve_spec P e
  calc
    _ = D ≫ ((Q.parameter Y).map k ≫ (Q.parameter Y).map l) := by rw [vSpec, ed, Category.assoc]
    _ = D ≫ (Q.parameter Y).map (k ≫ l) :=
      congrArg (fun z => D ≫ z) ((Q.parameter Y).map_comp k l).symm
    _ = _ := by rw [ekl, (Q.parameter Y).map_comp, ← Category.assoc, ← eDf]

end Silmaril.Calco2019.Proofs
