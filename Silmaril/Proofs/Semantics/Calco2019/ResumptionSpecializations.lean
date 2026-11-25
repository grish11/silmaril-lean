module

public import Silmaril.Semantics.Calco2019.ResumptionGuardThms
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Free.Thms
public import Silmaril.Semantics.Calco2019.ExceptionElgot
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits Exception

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

theorem resumption_iterative (M : ParametrizedGuardedElgotMonad P)
    (R : FinalResumptions M.toParametrizedMonad)
    (h : ∀ W : C, (M.obj W).guard.Iterative) : (M.resumptionGuardedness R).Iterative := by
  intro X Y f hsf
  let hf := (M.resumptionGuardedness_iff R f).mp hsf
  let r := M.resumptionFixpoints R
  refine ⟨r.iterate f hsf, r.fixpoint f hsf, ?_⟩
  intro g hg
  let Z := P.sum Y.of X.of
  let W := R.obj Z
  let V := R.obj Y.of
  let p : Z ⟶ V := P.desc (R.unit Y.of) g.of
  let k : W ⟶ V := R.extend P p
  let Q := (M.obj W).monad
  let Q' := (M.obj V).monad
  let v : X.of ⟶ Q.obj Z := f.of ≫ R.out Z
  let v' : X.of ⟶ Q'.obj Z := v ≫ (M.toParametrizedMonad.parameter Z).map k
  let a : Kleisli.mk Q' X.of ⟶ Kleisli.mk Q' Z := kleisliArrow v'
  let s : Kleisli.mk Q' X.of ⟶ Kleisli.mk Q' Y.of := kleisliArrow (g.of ≫ R.out Y.of)
  have ha : (M.obj V).guard.guarded (Y := Kleisli.mk Q' Y.of) (Z := Kleisli.mk Q' X.of) a :=
    (M.map k).guarded v hf
  have pf : f.of ≫ k = g.of := by
    have e := congrArg Kleisli.Hom.of hg
    change (f ≫ (P.kleisli (R.monad P)).desc (𝟙 Y) g).of = g.of at e
    rw [resumption_comp_of M R, kleisli_desc_of] at e
    exact e
  have eq : (f.of ≫ k) ≫ R.out Y.of =
      v' ≫ M.toParametrizedMonad.extend (W := V) (P.desc (Q'.η.app Y.of) s.of) := by
    have obs : k ≫ R.out Y.of = R.out Z ≫ (M.toParametrizedMonad.parameter Z).map k ≫
        M.toParametrizedMonad.extend (W := V) (p ≫ R.out Y.of) :=
      R.extend_spec P p
    have e : p ≫ R.out Y.of = P.desc (Q'.η.app Y.of) s.of := by
      change P.desc (R.unit Y.of) g.of ≫ R.out Y.of = _
      rw [P.desc_comp]
      exact congrArg (P.desc · s.of) (R.unit_out Y.of)
    rw [Category.assoc, obs, e]
    simp only [v', v, Category.assoc]
  have hs : Guardedness.IsFixpoint (P := P.kleisli Q') a s := by
    apply Kleisli.hom_ext
    change v' ≫ M.toParametrizedMonad.extend (W := V) ((P.kleisli Q').desc (𝟙 _) s).of = s.of
    rw [kleisli_desc_of]
    exact eq.symm.trans (congrArg (· ≫ R.out Y.of) pf)
  let b : Kleisli.mk Q' X.of ⟶ Kleisli.mk Q' Y.of := (M.obj V).iteration.iterate a ha
  obtain ⟨z, _, uniq⟩ := h V (Y := Kleisli.mk Q' Y.of) a ha
  have hbf : Guardedness.IsFixpoint (P := P.kleisli Q') a b :=
    (M.obj V).iteration.fixpoint (Y := Kleisli.mk Q' Y.of) a ha
  have hb : s = b := (uniq s hs).trans (uniq b hbf).symm
  have map_solution : M.diamond R f.of hf ≫ (M.toParametrizedMonad.parameter Y.of).map k = b.of :=
    (M.map k).iteration v hf
  have sol : R.IsSolution P (M.diamond R f.of hf) g.of :=
    (congrArg Kleisli.Hom.of hb).trans map_solution.symm
  apply Kleisli.hom_ext
  exact R.solve_unique P _ _ sol

theorem exception_iterative (T : GuardedElgotMonad P) (E : C) (h : T.guard.Iterative) :
    (fibre T E).guard.Iterative := by
  intro X Y f hf
  let Q := T.monad
  let L := (family P Q).obj E
  let K := P.kleisli Q
  let A := P.sum Y.of E
  let B := P.sum (P.sum Y.of X.of) E
  let sh : B ⟶ P.sum A X.of := rearrange P E
  let a : Kleisli.mk Q X.of ⟶ Kleisli.mk Q (P.sum A X.of) := kleisliArrow (f.of ≫ Q.map sh)
  let t := T.iteration.iterate a hf
  let p : X ⟶ Y := kleisliArrow t.of
  refine ⟨p, (fixpoints T E).fixpoint f hf, ?_⟩
  intro g hg
  let q : Kleisli.mk Q X.of ⟶ Kleisli.mk Q A := kleisliArrow g.of
  have ext : f.of ≫ extend P Q (P.desc (unit P Q E Y.of) g.of) = g.of := by
    have e := congrArg Kleisli.Hom.of hg
    change f.of ≫ (L.map ((P.kleisli L).desc (𝟙 Y) g).of ≫ L.μ.app Y.of) = g.of at e
    rw [kleisli_desc_of, family_extend] at e
    exact e
  have fix : Guardedness.IsFixpoint (P := K) a q := by
    apply Kleisli.hom_ext
    have e : sh ≫ P.desc (Q.η.app A) q.of = P.desc (P.desc (unit P Q E Y.of) q.of) (raise P Q E Y.of) := by
      simp [sh, A, rearrange, unit, raise]
    change (f.of ≫ Q.map sh) ≫ Q.map (K.desc (𝟙 _) q).of ≫ Q.μ.app A = g.of
    rw [kleisli_desc_of]
    change (f.of ≫ Q.map sh) ≫ Q.map (P.desc (Q.η.app A) q.of) ≫ Q.μ.app A = g.of
    rw [Category.assoc, ← Functor.map_comp_assoc, e]
    exact ext
  obtain ⟨z, _, uniq⟩ := h a hf
  have eq : q = t := (uniq q fix).trans (uniq t (T.iteration.fixpoint a hf)).symm
  exact Kleisli.hom_ext (congrArg (fun p : Kleisli.mk Q X.of ⟶ Kleisli.mk Q A => p.of) eq)


theorem resumption_freeObject [HasInitial C] {H : C ⥤ C}
    (R₀ : FinalResumptions (parametrizedElgot (guardedIdentity P) H).toParametrizedMonad) :
    (guardedBimodule P).IsFreeObject (resumptionGenerator R₀) := by
  let I := guardedIdentity_initial P
  have e : baseEmbedding (guardedIdentity P) H R₀ = I.to _ := I.hom_ext _ _
  exact (isFreeExtension_initial_iff I (resumptionGenerator R₀)).mp (e ▸ resumption_free R₀)

end Silmaril.Calco2019.Proofs
