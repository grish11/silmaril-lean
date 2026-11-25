module

public import Silmaril.Semantics.Calco2019.ResumptionGuardThms
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard
import Silmaril.Proofs.Semantics.Calco2019.ResumptionCodiagonal

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)

private theorem iterateResumption_congr {X Y : C} {f g : X ⟶ R.obj (P.sum Y X)}
    (e : f = g) (hf : M.ResumptionGuard R (Y := Y) (Z := X) f)
    (hg : M.ResumptionGuard R (Y := Y) (Z := X) g) :
    M.iterateResumption R f hf = M.iterateResumption R g hg := by
  subst g
  rfl

private theorem naturalityBody_of {X Y Z : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y X) (g : Y ⟶ Z) :
    (f ≫ (P.kleisli (R.monad P)).map g (𝟙 X)).of = M.naturalityBody R f.of g.of := by
  let T := R.monad P
  let K := P.kleisli T
  have e : (K.map g (𝟙 X)).of = P.desc (g.of ≫ T.map (P.inl (Y := X.of)))
      (P.inr ≫ R.unit (P.sum Z.of X.of)) := by
    change (K.desc (g ≫ K.inl) (𝟙 X ≫ K.inr)).of = _
    exact (kleisli_desc_of P T _ _).trans
      (congrArg₂ P.desc (comp_pure_of T g P.inl)
        (congrArg Kleisli.Hom.of (Category.id_comp (K.inr (X := Z) (Y := X)))))
  exact (resumption_comp_of M R f _).trans (congrArg (fun z => f.of ≫ R.extend P z) e)

theorem resumption_naturalCodiagonal : (M.resumptionFixpoints R).NaturalCodiagonal := by
  let T := R.monad P
  let K := P.kleisli T
  let I := M.resumptionFixpoints R
  constructor
  · intro X Y Z f g hf hg
    let h := f ≫ K.map g (𝟙 X)
    let hf' := (M.resumptionGuardedness_iff R f).mp hf
    let hh' := (M.resumptionGuardedness_iff R h).mp hg
    let hm := M.naturalityBody_guarded R f.of g.of hf'
    apply Kleisli.hom_ext
    have e₁ : (I.iterate h hg).of = M.iterateResumption R h.of hh' := rfl
    have e₂ := iterateResumption_congr M R (naturalityBody_of M R f g) hh' hm
    have e₃ := M.iterateResumption_naturality R f.of g.of hf'
    exact e₁.trans (e₂.trans (e₃.trans (resumption_comp_of M R (I.iterate f hf) g).symm))
  · intro X Y f hn hi ho hm
    let a := f ≫ K.assoc
    let s := I.iterate f hi
    let b := f ≫ K.merge
    have ea : a.of = f.of ≫ T.map (P.assoc (X := Y.of) (Y := X.of) (Z := X.of)) := by
      have e : K.assoc (X := Y) (Y := X) (Z := X) = (Kleisli.Adjunction.toKleisli T).map
          (P.assoc (X := Y.of) (Y := X.of) (Z := X.of)) := kleisli_assoc_pure T _ _ _
      exact (congrArg (fun j => (f ≫ j).of) e).trans (comp_pure_of T f P.assoc)
    have hn' : M.ResumptionNested R (X := Y.of) (Y := X.of) (Z := X.of) f.of :=
      Eq.mp (congrArg (M.ResumptionGuard R (Y := Y.of) (Z := P.sum X.of X.of)) ea)
        ((M.resumptionGuardedness_iff R a).mp hn)
    obtain ⟨hi', ho', hm', eq⟩ := iterateResumption_codiagonal M R f.of hn'
    have eb : b.of = f.of ≫ T.map (P.merge (X := X.of) (Y := Y.of)) :=
      (congrArg (fun j => (f ≫ j).of) (kleisli_merge_pure T X.of Y.of)).trans
        (comp_pure_of T f P.merge)
    apply Kleisli.hom_ext
    have e' := iterateResumption_congr M R eb ((M.resumptionGuardedness_iff R b).mp hm) hm'
    exact e'.trans (eq.trans (show _ = (I.iterate s ho).of from rfl))

theorem resumption_uniformity :
    (M.resumptionFixpoints R).Uniform (Kleisli.Adjunction.toKleisli (R.monad P)) := by
  let T := R.monad P
  let K := P.kleisli T
  let J := Kleisli.Adjunction.toKleisli T
  let I := M.resumptionFixpoints R
  intro X Z Y f g h hf hg comm
  have e : K.map (𝟙 Y) (J.map h) = J.map (P.map (𝟙 Y.of) h) := by
    have eid : 𝟙 Y = J.map (𝟙 Y.of) := (J.map_id _).symm
    rw [eid]
    exact kleisli_map_pure T _ _
  have c : h ≫ f.of = g.of ≫ T.map (P.map (𝟙 Y.of) h) :=
    (pure_comp_of T h f).symm.trans ((congrArg Kleisli.Hom.of comm).trans
      ((congrArg (fun j => (g ≫ j).of) e).trans (comp_pure_of T g _)))
  apply Kleisli.hom_ext
  exact (pure_comp_of T h (I.iterate f hf)).trans
    (M.iterateResumption_uniform R f.of g.of h
      ((M.resumptionGuardedness_iff R f).mp hf) ((M.resumptionGuardedness_iff R g).mp hg) c)

end Silmaril.Calco2019.Proofs
