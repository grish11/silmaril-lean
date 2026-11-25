module

public import Silmaril.Semantics.Calco2019.Maybe.LoopDecomposition.Defs
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Maybe.Proofs

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {P : Coproducts C} {X Y : C}
  (T : GuardedElgotMonad P) (total : T.IsElgot)

open Silmaril.Calco2019.Proofs

theorem iteratePure_zero {f : X ⟶ P.sum Y X} (D : LoopDecomposition f) :
    D.finiteIn 0 ≫ iteratePure T total f = D.result ≫ T.monad.η.app Y := by
  let Q := P.kleisli T.monad
  let J := Kleisli.Adjunction.toKleisli T.monad
  let b : J.obj X ⟶ Q.sum (J.obj Y) (J.obj X) := J.map f
  let solution : J.obj X ⟶ J.obj Y := T.iteration.iterate b (total b)
  have unfold := T.iteration.fixpoint b (total b)
  change b ≫ Q.desc (𝟙 (J.obj Y)) solution = solution at unfold
  have e : J.map (D.finiteIn 0) ≫ solution = J.map D.result := calc
    _ = J.map (D.finiteIn 0) ≫ (b ≫ Q.desc (𝟙 (J.obj Y)) solution) :=
      congrArg (J.map (D.finiteIn 0) ≫ ·) unfold.symm
    _ = J.map (D.finiteIn 0 ≫ f) ≫ Q.desc (𝟙 (J.obj Y)) solution := by
      rw [J.map_comp, Category.assoc]
    _ = _ := by
      rw [D.zero_eq, J.map_comp, Category.assoc]
      change J.map D.result ≫ Q.inl ≫ Q.desc (𝟙 (J.obj Y)) solution = _
      simp
  have lhs := pure_comp_of T.monad (D.finiteIn 0) solution
  exact lhs.symm.trans (congrArg Kleisli.Hom.of e)

theorem iteratePure_succ {f : X ⟶ P.sum Y X} (D : LoopDecomposition f) (n : ℕ) :
    D.finiteIn (n + 1) ≫ iteratePure T total f =
      D.advance n ≫ D.finiteIn n ≫ iteratePure T total f := by
  let Q := P.kleisli T.monad
  let J := Kleisli.Adjunction.toKleisli T.monad
  let b : J.obj X ⟶ Q.sum (J.obj Y) (J.obj X) := J.map f
  let solution : J.obj X ⟶ J.obj Y := T.iteration.iterate b (total b)
  have unfold := T.iteration.fixpoint b (total b)
  change b ≫ Q.desc (𝟙 (J.obj Y)) solution = solution at unfold
  have e : J.map (D.finiteIn (n + 1)) ≫ solution = J.map (D.advance n ≫ D.finiteIn n) ≫ solution := calc
    _ = J.map (D.finiteIn (n + 1)) ≫ (b ≫ Q.desc (𝟙 (J.obj Y)) solution) :=
      congrArg (J.map (D.finiteIn (n + 1)) ≫ ·) unfold.symm
    _ = J.map (D.finiteIn (n + 1) ≫ f) ≫ Q.desc (𝟙 (J.obj Y)) solution := by
      rw [J.map_comp, Category.assoc]
    _ = _ := by
      rw [D.succ_eq, ← Category.assoc, J.map_comp, Category.assoc]
      change J.map (D.advance n ≫ D.finiteIn n) ≫ Q.inr ≫ Q.desc (𝟙 (J.obj Y)) solution = _
      simp
  exact (pure_comp_of T.monad _ solution).symm.trans
    ((congrArg Kleisli.Hom.of e).trans ((pure_comp_of T.monad _ solution).trans (Category.assoc _ _ _)))

theorem iteratePure_residual {f : X ⟶ P.sum Y X} (D : LoopDecomposition f)
    {E : C} (terminal : IsTerminal E) :
    D.residualIn ≫ iteratePure T total f =
      terminal.from D.residual ≫ divergence T total E Y := by
  let Q := P.kleisli T.monad
  let J := Kleisli.Adjunction.toKleisli T.monad
  let b : J.obj X ⟶ Q.sum (J.obj Y) (J.obj X) := J.map f
  let r : J.obj D.residual ⟶ Q.sum (J.obj Y) (J.obj D.residual) := J.map (D.residualStep ≫ P.inr)
  let forever : J.obj E ⟶ Q.sum (J.obj Y) (J.obj E) := Q.inr
  have square : J.map D.residualIn ≫ b = r ≫ Q.map (𝟙 (J.obj Y)) (J.map D.residualIn) := by
    calc
      _ = J.map (D.residualIn ≫ f) := (J.map_comp _ _).symm
      _ = _ := by
        rw [D.residual_eq, J.map_comp, J.map_comp]
        change J.map D.residualStep ≫ J.map D.residualIn ≫ Q.inr = _
        rw [show r = J.map D.residualStep ≫ Q.inr from J.map_comp _ _]
        simp [Coproducts.map]
  have foreverSquare : J.map (terminal.from D.residual) ≫ forever =
      r ≫ Q.map (𝟙 (J.obj Y)) (J.map (terminal.from D.residual)) := by
    rw [show r = J.map D.residualStep ≫ Q.inr from J.map_comp _ _]
    change _ = (J.map D.residualStep ≫ Q.inr) ≫
      Q.desc (𝟙 (J.obj Y) ≫ Q.inl) (J.map (terminal.from D.residual) ≫ Q.inr)
    simp only [Category.assoc, Coproducts.inr_desc]
    rw [← Category.assoc, ← J.map_comp, terminal.hom_ext
      (D.residualStep ≫ terminal.from D.residual) (terminal.from D.residual)]
  have e := congrArg Kleisli.Hom.of (T.uniformity b r D.residualIn (total b) (total r) square)
  have d := congrArg Kleisli.Hom.of (T.uniformity forever r (terminal.from D.residual)
    (total forever) (total r) foreverSquare)
  exact (pure_comp_of T.monad D.residualIn _).symm.trans
    (e.trans (d.symm.trans (pure_comp_of T.monad (terminal.from D.residual) _)))


theorem comparison_iteratePure [HasInitial C] {E : C} (terminal : IsTerminal E)
    (S : GuardedElgotMonad P) (hs : S.IsElgot) (hm : S.monad = monad P E)
    {f : X ⟶ P.sum Y X} (D : LoopDecomposition f) :
    iteratePure S hs f ≫ eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) ≫
      (comparison T total E).app Y = iteratePure T total f := by
  obtain ⟨M, G, F, U⟩ := S
  change M = monad P E at hm
  subst M
  let S : GuardedElgotMonad P := ⟨monad P E, G, F, U⟩
  change iteratePure S hs f ≫ _ ≫ (comparison T total E).app Y = _
  rw [eqToHom_refl, Category.id_comp]
  apply D.isColimit.hom_ext
  rintro ⟨i⟩
  cases i with
  | none =>
    change D.residualIn ≫ (iteratePure S hs f ≫ (comparison T total E).app Y) =
      D.residualIn ≫ iteratePure T total f
    have fail := divergence_eq_failure terminal S hs rfl Y
    change divergence S hs E Y ≫ 𝟙 (S.monad.obj Y) = _ at fail
    rw [Category.comp_id] at fail
    rw [← Category.assoc, iteratePure_residual S hs D terminal, Category.assoc,
      iteratePure_residual T total D terminal, fail]
    exact congrArg (terminal.from D.residual ≫ ·) (P.inr_desc _ _)
  | some n =>
    change D.finiteIn n ≫ (iteratePure S hs f ≫ (comparison T total E).app Y) =
      D.finiteIn n ≫ iteratePure T total f
    induction n with
    | zero =>
      rw [← Category.assoc, iteratePure_zero S hs D, Category.assoc, iteratePure_zero T total D]
      exact congrArg (D.result ≫ ·) ((comparison T total E).app_η Y)
    | succ n ih =>
      rw [← Category.assoc, iteratePure_succ S hs D, Category.assoc, Category.assoc,
        iteratePure_succ T total D, ih]


private theorem iteratePure_natural {B : C} (f : X ⟶ P.sum B X) (k : B ⟶ T.monad.obj Y) :
    let b := f ≫ P.desc (k ≫ T.monad.map (P.inl (Y := X))) (P.inr ≫ T.monad.η.app (P.sum Y X))
    iteratePure T total f ≫ T.monad.map k ≫ T.monad.μ.app Y =
      (T.iteration.iterate (kleisliArrow b) (total (kleisliArrow b))).of := by
  let Q := P.kleisli T.monad
  let J := Kleisli.Adjunction.toKleisli T.monad
  let body : J.obj X ⟶ Q.sum (J.obj B) (J.obj X) := J.map f
  let cont : J.obj B ⟶ J.obj Y := kleisliArrow k
  let mapped := body ≫ Q.map cont (𝟙 (J.obj X))
  have e := T.iteration.naturalCodiagonal.naturality body cont (total body) (total mapped)
  have mappedOf : mapped.of =
      f ≫ P.desc (k ≫ T.monad.map (P.inl (Y := X))) (P.inr ≫ T.monad.η.app (P.sum Y X)) := by
    rw [show mapped.of = f ≫ (Q.map cont (𝟙 (J.obj X))).of from pure_comp_of T.monad f _]
    change f ≫ (Q.desc (cont ≫ Q.inl) (𝟙 (J.obj X) ≫ Q.inr)).of = _
    rw [Category.id_comp, kleisli_desc_of]
    exact congrArg (fun leg => f ≫ P.desc leg Q.inr.of) (comp_pure_of T.monad cont P.inl)
  refine (congrArg Kleisli.Hom.of e).symm.trans ?_
  exact congrArg (fun m => (T.iteration.iterate m (total m)).of) (Kleisli.hom_ext mappedOf)

private def reorder (P : Coproducts C) (E : C) : P.sum (P.sum Y X) E ⟶ P.sum (P.sum Y E) X :=
  P.desc (P.map P.inl (𝟙 X)) (P.inr ≫ P.inl)

private theorem interpret_reorder (E : C) :
    reorder (X := X) (Y := Y) P E ≫
        P.desc (interpret T total E Y ≫ T.monad.map (P.inl (Y := X)))
          (P.inr ≫ T.monad.η.app (P.sum Y X)) =
      interpret T total E (P.sum Y X) := by
  rw [reorder, P.desc_comp]
  change _ = P.desc (T.monad.η.app (P.sum Y X)) (divergence T total E (P.sum Y X))
  apply P.hom_ext
  · rw [P.inl_desc, P.inl_desc, P.map_desc]
    apply P.hom_ext
    · simpa [interpret] using (T.monad.η.naturality (P.inl (X := Y) (Y := X))).symm
    · simp
  · rw [P.inr_desc, Category.assoc, P.inl_desc]
    change P.inr ≫ P.desc (T.monad.η.app Y) (divergence T total E Y) ≫ _ = _
    have e := divergence_natural T total (X := E)
      (P.inl (X := Y) (Y := X) ≫ T.monad.η.app (P.sum Y X))
    rw [Functor.map_comp, Category.assoc, T.monad.right_unit, Category.comp_id] at e
    exact (P.inr_desc_assoc _ _ _).trans (e.trans (P.inr_desc _ _).symm)

set_option maxHeartbeats 400000 in
theorem comparison_iterates [HasInitial C] {E : C} (terminal : IsTerminal E)
    (S : GuardedElgotMonad P) (hs : S.IsElgot) (hm : S.monad = monad P E)
    (decompose : ∀ {A B : C} (f : A ⟶ P.sum B A), Nonempty (LoopDecomposition f))
    (f : X ⟶ S.monad.obj (P.sum Y X)) :
    let m (Y : C) := eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) ≫
      (comparison T total E).app Y
    (S.iteration.iterate (kleisliArrow f) (hs (kleisliArrow f))).of ≫ m Y =
      (T.iteration.iterate (kleisliArrow (f ≫ m (P.sum Y X)))
        (total (kleisliArrow (f ≫ m (P.sum Y X))))).of := by
  obtain ⟨M, G, F, U⟩ := S
  change M = monad P E at hm
  subst M
  let S : GuardedElgotMonad P := ⟨monad P E, G, F, U⟩
  simp only [eqToHom_refl, Category.id_comp]
  change X ⟶ P.sum (P.sum Y X) E at f
  let g := f ≫ reorder (X := X) (Y := Y) P E
  obtain ⟨D⟩ := decompose g
  let m := comparison T total E
  let k := interpret S hs E Y
  have interpretSelf (Z : C) : interpret S hs E Z = 𝟙 (P.sum Z E) := by
    have e := divergence_eq_failure terminal S hs rfl Z
    change divergence S hs E Z ≫ 𝟙 (P.sum Z E) = _ at e
    have hη : S.monad.η.app Z = P.inl := by
      change P.inl ≫ 𝟙 (P.sum Z E) = P.inl
      simp
    have fail := (Category.comp_id (divergence S hs E Z)).symm.trans e
    change P.desc (S.monad.η.app Z) (divergence S hs E Z) = _
    rw [hη, fail, P.desc_inl_inr]
    rfl
  have kmap : k ≫ m.app Y = interpret T total E Y := by
    change interpret S hs E Y ≫ interpret T total E Y = _
    rw [interpretSelf, Category.id_comp]
  have source := iteratePure_natural S hs g k
  have target := iteratePure_natural T total g (interpret T total E Y)
  dsimp only at source target
  rw [show g = f ≫ reorder P E from rfl, Category.assoc, interpret_reorder,
    interpretSelf (P.sum Y X), Category.comp_id] at source
  rw [show g = f ≫ reorder P E from rfl, Category.assoc, interpret_reorder] at target
  have pureComparison := comparison_iteratePure T total terminal S hs rfl D
  rw [eqToHom_refl, Category.id_comp] at pureComparison
  change (_ ≫ m.app Y) =
    (T.iteration.iterate (kleisliArrow (f ≫ interpret T total E (P.sum Y X)))
      (total (kleisliArrow (f ≫ interpret T total E (P.sum Y X))))).of
  rw [← source, ← target]
  change (iteratePure S hs g ≫ S.monad.map k ≫ S.monad.μ.app Y) ≫ m.app Y =
    iteratePure T total g ≫ T.monad.map (interpret T total E Y) ≫ T.monad.μ.app Y
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (iteratePure S hs g ≫ ·) (map_extension m k)).trans ?_
  change iteratePure S hs g ≫ (m.app (P.sum Y E) ≫ T.monad.map (k ≫ m.app Y) ≫ T.monad.μ.app Y) = _
  change iteratePure S hs g ≫ m.app (P.sum Y E) = iteratePure T total g at pureComparison
  rw [kmap, ← Category.assoc (iteratePure S hs g), pureComparison]

end Silmaril.Calco2019.Maybe.Proofs
