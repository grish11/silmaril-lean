module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Defs
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard
import Silmaril.Proofs.Semantics.Calco2019.ExceptionSuspension

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (H : C ⥤ C)
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

private lemma parameter_map {X A B : C} (f : A ⟶ B) :
    ((parametrizedElgot T H).toParametrizedMonad.parameter X).map f =
      T.monad.map (P.map (𝟙 X) (H.map f)) := rfl

private lemma parameter_extend {W X Y : C} (f : X ⟶ T.monad.obj (P.sum Y (H.obj W))) :
    (parametrizedElgot T H).toParametrizedMonad.extend (W := W) f =
      extend P T.monad f :=
  family_extend P T.monad (H.obj W) f

private lemma map_inl_parameter {X W W' : C} (f : W ⟶ W') :
    T.monad.map (P.inl (X := X) (Y := H.obj W)) ≫
      ((parametrizedElgot T H).toParametrizedMonad.parameter X).map f =
        T.monad.map (P.inl (X := X) (Y := H.obj W')) := by
  rw [parameter_map, ← Functor.map_comp]
  simp [Coproducts.map]

@[reassoc]
theorem base_out (X : C) :
    liftBase T H R X ≫ R.out X = T.monad.map (P.inl (Y := H.obj (R.obj X))) := by
  unfold liftBase
  rw [Category.assoc, R.roll_out]
  exact Category.comp_id _

theorem base_unit (X : C) : T.monad.η.app X ≫ liftBase T H R X = R.unit X := by
  change T.monad.η.app X ≫ T.monad.map P.inl ≫ R.roll X =
    (P.inl ≫ T.monad.η.app (P.sum X (H.obj (R.obj X)))) ≫ R.roll X
  exact (T.monad.η.naturality_assoc P.inl (R.roll X)).symm.trans
    (Category.assoc _ _ _).symm

theorem base_extend {X Y : C} (f : X ⟶ T.monad.obj Y) :
    (KleisliTriple.ofMonad T.monad).extend f ≫ liftBase T H R Y =
      liftBase T H R X ≫ R.extend P (f ≫ liftBase T H R Y) := by
  let Q := T.monad
  let k := R.extend P (f ≫ liftBase T H R Y)
  let E := H.obj (R.obj Y)
  let A := P.sum Y E
  have obs := R.extend_spec P (f ≫ liftBase T H R Y)
  have ep : (f ≫ liftBase T H R Y) ≫ R.out Y = f ≫ Q.map (P.inl (Y := E)) := by
    exact (Category.assoc _ _ _).trans (congrArg (f ≫ ·) (base_out T H R Y))
  rw [ep, parameter_extend] at obs
  have er : liftBase T H R X ≫ k ≫ R.out Y =
      Q.map (P.inl (Y := E)) ≫ extend P Q (f ≫ Q.map (P.inl (Y := E))) := by
    rw [show k ≫ R.out Y = _ from obs, ← Category.assoc, base_out]
    rw [← Category.assoc, map_inl_parameter T H]
  have eb : Q.map (P.inl (X := X) (Y := E)) ≫ extend P Q (f ≫ Q.map (P.inl (Y := E))) =
      (Q.map f ≫ Q.μ.app Y) ≫ Q.map (P.inl (Y := E)) := by
    change Q.map P.inl ≫ Q.map (P.desc (f ≫ Q.map P.inl) (raise P Q E Y)) ≫ Q.μ.app A =
      (Q.map f ≫ Q.μ.app Y) ≫ Q.map P.inl
    have hm : Q.μ.app Y ≫ Q.map (P.inl (Y := E)) =
        Q.map (Q.map P.inl) ≫ Q.μ.app A :=
      (Q.μ.naturality (P.inl (Y := E))).symm
    simp only [Category.assoc, ← Functor.map_comp_assoc, Coproducts.inl_desc, hm]
  have e : ((KleisliTriple.ofMonad T.monad).extend f ≫ liftBase T H R Y) ≫ R.out Y =
      (liftBase T H R X ≫ k) ≫ R.out Y := by
    rw [Category.assoc, base_out]
    exact ((eb.symm.trans er.symm).trans (Category.assoc _ _ _).symm)
  simpa only [Category.assoc, R.out_roll, Category.comp_id] using congrArg (· ≫ R.roll Y) e

theorem base_nat {X Y : C} (h : X ⟶ Y) :
    T.monad.map h ≫ liftBase T H R Y = liftBase T H R X ≫ (R.monad P).map h := by
  have h' := base_extend T H R (h ≫ T.monad.η.app Y)
  have e : (KleisliTriple.ofMonad T.monad).extend (h ≫ T.monad.η.app Y) = T.monad.map h := by
    change T.monad.map (h ≫ T.monad.η.app Y) ≫ T.monad.μ.app Y = _
    simp
  rw [e] at h'
  refine h'.trans ?_
  exact congrArg (fun b => liftBase T H R X ≫ R.extend P b)
    ((Category.assoc _ _ _).trans (congrArg (h ≫ ·) (base_unit T H R Y)))

theorem resumption_map_out {X Y : C} (f : X ⟶ Y) :
    (R.monad P).map f ≫ R.out Y =
      R.out X ≫ T.monad.map (P.map f (H.map ((R.monad P).map f))) :=
  Proofs.resumption_map_outFor P T.monad H R f

private theorem base_normalized {X Y Z : C}
    (f : X ⟶ T.monad.obj (P.sum Y Z)) :
    let E := H.obj (R.obj (P.sum Y Z))
    ((f ≫ liftBase T H R (P.sum Y Z)) ≫ R.out (P.sum Y Z)) ≫ T.monad.map (rearrange P E) =
      f ≫ T.monad.map (P.map (P.inl (X := Y) (Y := E)) (𝟙 Z)) := by
  intro E
  have eq : P.inl ≫ rearrange P E (Y := Y) (Z := Z) = P.map P.inl (𝟙 Z) := by
    simp [rearrange, Coproducts.map]
  rw [Category.assoc, Category.assoc, base_out_assoc, ← Functor.map_comp, eq]

private theorem normalized_base_kleisli {X Y Z : C}
    (f : X ⟶ T.monad.obj (P.sum Y Z)) :
    let E := H.obj (R.obj (P.sum Y Z))
    let Q := T.monad
    let J := Kleisli.Adjunction.toKleisli Q
    let K := P.kleisli Q
    (kleisliArrow (((f ≫ liftBase T H R (P.sum Y Z)) ≫ R.out (P.sum Y Z)) ≫
      Q.map (rearrange P E)) : Kleisli.mk Q X ⟶ Kleisli.mk Q (P.sum (P.sum Y E) Z)) =
      kleisliArrow f ≫ K.map (J.map (P.inl (X := Y) (Y := E))) (𝟙 (Kleisli.mk Q Z)) := by
  intro E Q J K
  have hid : 𝟙 (Kleisli.mk Q Z) = J.map (𝟙 Z) := (J.map_id Z).symm
  rw [hid, kleisli_map_pure]
  exact Kleisli.hom_ext ((base_normalized T H R f).trans (comp_pure_of Q (kleisliArrow f) _).symm)

theorem base_guard {X Y Z : C} (f : X ⟶ T.monad.obj (P.sum Y Z))
    (hf : T.guard.guarded (Y := Kleisli.mk T.monad Y) (Z := Kleisli.mk T.monad Z)
      (kleisliArrow f)) :
    (parametrizedElgot T H).ResumptionGuard R (Y := Y) (Z := Z)
      (f ≫ liftBase T H R (P.sum Y Z)) := by
  let Q := T.monad
  let E := H.obj (R.obj (P.sum Y Z))
  change T.guard.guarded (Y := Kleisli.mk Q (P.sum Y E)) (Z := Kleisli.mk Q Z)
    (kleisliArrow (((f ≫ liftBase T H R (P.sum Y Z)) ≫ R.out (P.sum Y Z)) ≫ Q.map (rearrange P E)))
  rw [normalized_base_kleisli T H R f]
  exact Guardedness.map hf _ _

theorem base_iteration {X Y : C} (f : X ⟶ T.monad.obj (P.sum Y X))
    (hf : T.guard.guarded (Y := Kleisli.mk T.monad Y) (Z := Kleisli.mk T.monad X)
      (kleisliArrow f)) :
    (T.iteration.iterate (kleisliArrow f) hf).of ≫ liftBase T H R Y =
      (parametrizedElgot T H).iterateResumption R (f ≫ liftBase T H R (P.sum Y X))
        (base_guard T H R f hf) := by
  let M := parametrizedElgot T H
  let Q := T.monad
  let K := P.kleisli Q
  let J := Kleisli.Adjunction.toKleisli Q
  let E := H.obj (R.obj (P.sum Y X))
  let a : Kleisli.mk Q X ⟶ Kleisli.mk Q (P.sum Y X) := kleisliArrow f
  let j : Y ⟶ P.sum Y E := P.inl
  let j' := J.map j
  let b := a ≫ K.map j' (𝟙 (Kleisli.mk Q X))
  let g := T.iteration.iterate a hf
  let g' := g.of ≫ liftBase T H R Y
  let hbody := base_guard T H R f hf
  have hb : T.guard.guarded (Y := Kleisli.mk Q (P.sum Y E)) (Z := Kleisli.mk Q X) b :=
    Guardedness.map hf _ _
  have h := iterate_congr T.iteration.toFixpoints (normalized_base_kleisli T H R f) hbody hb
  have n := T.iteration.naturalCodiagonal.naturality a j' hf hb
  let d := M.diamond R (f ≫ liftBase T H R (P.sum Y X)) hbody
  have hd : d = g.of ≫ Q.map j :=
    (congrArg (fun k : Kleisli.mk Q X ⟶ Kleisli.mk Q (P.sum Y E) => k.of) (h.trans n)).trans
      (comp_pure_of Q g j)
  have solution : R.IsSolution P d g' := by
    let k := R.extend P (P.desc (R.unit Y) g')
    change (g.of ≫ liftBase T H R Y) ≫ R.out Y = d ≫ (M.toParametrizedMonad.parameter Y).map k
    rw [hd, Category.assoc, base_out, Category.assoc, map_inl_parameter T H]
  exact R.solve_unique P d g' solution

theorem base_mul (X : C) :
    T.monad.μ.app X ≫ liftBase T H R X =
      (T.monad.map (liftBase T H R X) ≫ liftBase T H R (R.obj X)) ≫ (R.monad P).μ.app X := by
  have h := base_extend T H R (𝟙 (T.monad.obj X))
  change (T.monad.map (𝟙 (T.monad.obj X)) ≫ T.monad.μ.app X) ≫ liftBase T H R X =
    liftBase T H R (T.monad.obj X) ≫ R.extend P (𝟙 (T.monad.obj X) ≫ liftBase T H R X) at h
  simp only [Functor.map_id, Category.id_comp] at h
  rw [base_nat T H R (liftBase T H R X), Category.assoc, R.monad_extend]
  exact h

end Silmaril.Calco2019.Proofs
