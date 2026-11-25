module

public import Silmaril.Semantics.Calco2019.Maybe.Defs

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Maybe.Proofs

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (total : T.IsElgot)

theorem divergence_natural {X Y Z : C} (g : Y ⟶ T.monad.obj Z) :
    divergence T total X Y ≫ T.monad.map g ≫ T.monad.μ.app Z =
      divergence T total X Z := by
  let Q := P.kleisli T.monad
  let f : Kleisli.mk T.monad X ⟶ Q.sum (Kleisli.mk T.monad Y) (.mk T.monad X) := Q.inr
  let j : Kleisli.mk T.monad Y ⟶ Kleisli.mk T.monad Z := kleisliArrow g
  have eq : f ≫ Q.map j (𝟙 _) = Q.inr := by
    change Q.inr ≫ Q.desc (j ≫ Q.inl) (𝟙 _ ≫ Q.inr) = Q.inr
    simp
  have e := T.iteration.naturalCodiagonal.naturality f j (total f) (total _)
  have q := congrArg (fun b => T.iteration.iterate b (total b)) eq
  exact congrArg Kleisli.Hom.of (e.symm.trans q)

theorem divergence_uniform {X Z Y : C} (h : Z ⟶ X) :
    h ≫ divergence T total X Y = divergence T total Z Y := by
  let Q := P.kleisli T.monad
  let J := Kleisli.Adjunction.toKleisli T.monad
  let f : J.obj X ⟶ Q.sum (.mk T.monad Y) (J.obj X) := Q.inr
  let g : J.obj Z ⟶ Q.sum (.mk T.monad Y) (J.obj Z) := Q.inr
  have square : J.map h ≫ f = g ≫ Q.map (𝟙 (Kleisli.mk T.monad Y)) (J.map h) := by
    change J.map h ≫ Q.inr = Q.inr ≫ Q.desc (𝟙 _ ≫ Q.inl) (J.map h ≫ Q.inr)
    simp
  have e := congrArg Kleisli.Hom.of (T.uniformity f g h (total f) (total g) square)
  change (h ≫ T.monad.η.app X) ≫
    (T.monad.map (divergence T total X Y) ≫ T.monad.μ.app Y) =
    divergence T total Z Y at e
  simpa only [Category.assoc, (KleisliTriple.ofMonad T.monad).unit_extend] using e


theorem monadMap_extend (E : C) {X Y : C} (f : X ⟶ P.sum Y E) :
    (KleisliTriple.ofMonad (monad P E)).extend f ≫ interpret T total E Y =
      interpret T total E X ≫ (KleisliTriple.ofMonad T.monad).extend (f ≫ interpret T total E Y) := by
  change (((monad P E).map f) ≫ (monad P E).μ.app Y) ≫ _ = _
  refine (congrArg (· ≫ interpret T total E Y)
    (Exception.family_extend P (CategoryTheory.Monad.id C) E f)).trans ?_
  have extendId : Exception.extend P (CategoryTheory.Monad.id C) f = P.desc f P.inr := by
    change (P.desc f (P.inr ≫ 𝟙 (P.sum Y E)) ≫ 𝟙 _) = _
    rw [Category.comp_id, show (P.inr (X := Y) (Y := E)) ≫ 𝟙 _ = P.inr by simp]
  refine (congrArg (· ≫ interpret T total E Y) extendId).trans ?_
  change P.desc f (P.inr (X := Y) (Y := E)) ≫ interpret T total E Y =
    interpret T total E X ≫ (T.monad.map (f ≫ interpret T total E Y) ≫ T.monad.μ.app Y)
  apply P.hom_ext
  · simpa only [Category.assoc, Coproducts.inl_desc_assoc, interpret] using
      ((KleisliTriple.ofMonad T.monad).unit_extend (f ≫ interpret T total E Y)).symm
  · simpa only [Category.assoc, Coproducts.inr_desc_assoc, interpret, Coproducts.inr_desc] using
      (divergence_natural T total (X := E) (f ≫ interpret T total E Y)).symm

theorem map_naturality (E : C) {X Y : C} (f : X ⟶ Y) :
    (monad P E).map f ≫ interpret T total E Y = interpret T total E X ≫ T.monad.map f := by
  rw [Exception.family_map]
  change P.map f (𝟙 E) ≫ _ = _
  apply P.hom_ext
  · simpa [interpret, Coproducts.map] using T.monad.η.naturality f
  · simp only [interpret, Coproducts.map_desc, Coproducts.inr_desc, Category.id_comp,
      Coproducts.inr_desc_assoc]
    have h := divergence_natural T total (X := E) (f ≫ T.monad.η.app Y)
    rw [Functor.map_comp, Category.assoc, T.monad.right_unit, Category.comp_id] at h
    exact h.symm

theorem map_mul (E X : C) :
    (monad P E).μ.app X ≫ interpret T total E X =
      ((monad P E).map (interpret T total E X) ≫ interpret T total E (T.monad.obj X)) ≫
        T.monad.μ.app X := by
  have h := monadMap_extend T total E (𝟙 ((monad P E).obj X))
  change ((monad P E).map (𝟙 _) ≫ (monad P E).μ.app X) ≫ interpret T total E X =
    interpret T total E ((monad P E).obj X) ≫
      T.monad.map (𝟙 _ ≫ interpret T total E X) ≫ T.monad.μ.app X at h
  have idSimplified : (𝟙 ((monad P E).obj X) ≫ interpret T total E X) =
      interpret T total E X := Category.id_comp _
  rw [Functor.map_id, Category.id_comp, idSimplified] at h
  refine h.trans ((Category.assoc _ _ _).symm.trans ?_)
  exact congrArg (· ≫ T.monad.μ.app X) (map_naturality T total E (interpret T total E X)).symm


theorem divergence_morphism {S : GuardedElgotMonad P} (hs : S.IsElgot)
    (m : GuardedElgotMonadHom P S T) (X Y : C) :
    divergence S hs X Y ≫ m.hom.app Y = divergence T total X Y := by
  let f : X ⟶ S.monad.obj (P.sum Y X) := P.inr ≫ S.monad.η.app (P.sum Y X)
  have e := m.iteration f (hs (kleisliArrow f))
  have body : f ≫ m.hom.app (P.sum Y X) = P.inr ≫ T.monad.η.app (P.sum Y X) := by
    simp [f]
  refine e.trans ?_
  exact congrArg (fun b => (T.iteration.iterate (kleisliArrow b)
    (total (kleisliArrow b))).of) body

theorem maybe_divergence [HasInitial C] {E : C} (terminal : IsTerminal E)
    (S : GuardedElgotMonad P) (hs : S.IsElgot) (hm : S.monad = monad P E) (Y : C) :
    divergence S hs E Y ≫ eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) =
      P.inr := by
  obtain ⟨M, G, F, U⟩ := S
  change M = monad P E at hm
  subst M
  simp only [eqToHom_refl, Category.comp_id]
  let S : GuardedElgotMonad P := ⟨monad P E, G, F, U⟩
  change divergence S hs E Y = P.inr
  have e := divergence_natural S hs (X := E) (initial.to Y ≫ S.monad.η.app Y)
  -- Pick the empty result explicitly so the only possible output of the pure loop is failure.
  change divergence S hs E (⊥_ C) ≫
    S.monad.map (initial.to Y ≫ S.monad.η.app Y) ≫ S.monad.μ.app Y = _ at e
  rw [Functor.map_comp, Category.assoc, S.monad.right_unit, Category.comp_id] at e
  change divergence S hs E (⊥_ C) ≫ (monad P E).map (initial.to Y) = _ at e
  have mapEq : (monad P E).map (initial.to Y) =
      P.desc (initial.to E) (𝟙 E) ≫ P.inr := by
    have mapId := Exception.family_map P (CategoryTheory.Monad.id C) E (initial.to Y)
    refine mapId.trans ?_
    change P.map (initial.to Y) (𝟙 E) = _
    apply P.hom_ext
    · exact initialIsInitial.hom_ext _ _
    · simp [Coproducts.map]
  refine e.symm.trans ((congrArg (divergence S hs E (⊥_ C) ≫ ·) mapEq).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ P.inr) (terminal.hom_ext
    (divergence S hs E (⊥_ C) ≫ P.desc (initial.to E) (𝟙 E)) (𝟙 E))).trans (Category.id_comp _)

theorem morphism_unique [HasInitial C] {E : C} (terminal : IsTerminal E)
    (S : GuardedElgotMonad P) (hs : S.IsElgot) (hm : S.monad = monad P E)
    (m : GuardedElgotMonadHom P S T) (Y : C) :
    m.hom.app Y = eqToHom (congrArg (fun M : CategoryTheory.Monad C => M.obj Y) hm) ≫
      interpret T total E Y := by
  obtain ⟨M, G, F, U⟩ := S
  change M = monad P E at hm
  subst M
  simp only [eqToHom_refl]
  refine Eq.trans ?_ (Category.id_comp (interpret T total E Y)).symm
  change (_ : P.sum Y E ⟶ T.monad.obj Y) = interpret T total E Y
  apply P.hom_ext
  · have h := m.hom.app_η Y
    have i : (monad P E).η.app Y = P.inl := by
      change P.inl ≫ 𝟙 _ = _
      simp
    exact (congrArg (· ≫ m.hom.app Y) i).symm.trans (h.trans (P.inl_desc _ _).symm)
  · let S : GuardedElgotMonad P := ⟨monad P E, G, F, U⟩
    have h := maybe_divergence terminal S hs rfl Y
    change divergence S hs E Y ≫ 𝟙 (S.monad.obj Y) = _ at h
    have d := (Category.comp_id (divergence S hs E Y)).symm.trans h
    exact (congrArg (· ≫ m.hom.app Y) d).symm.trans
      ((divergence_morphism T total hs m E Y).trans (P.inr_desc _ _).symm)

end Silmaril.Calco2019.Maybe.Proofs
