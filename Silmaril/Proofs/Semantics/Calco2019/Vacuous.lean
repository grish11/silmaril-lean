module

public import Silmaril.Semantics.Calco2019.Vacuous

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  {T : CategoryTheory.Monad C} {S : GuardedElgotMonad P}

private theorem post_inl_of {X Y Z : C} (g : Kleisli.mk T X ⟶ Kleisli.mk T Y) :
    (g ≫ (P.kleisli T).inl (Y := Kleisli.mk T Z)).of = g.of ≫ T.map P.inl := by
  change g.of ≫ T.map (P.inl ≫ T.η.app (P.sum Y Z)) ≫ T.μ.app (P.sum Y Z) = _
  simp

private theorem factor_map (m : T ⟶ S.monad) {X Y Z : C}
    (f : X ⟶ T.obj (P.sum Y Z)) (g : Kleisli.mk T X ⟶ Kleisli.mk T Y)
    (e : kleisliArrow f = g ≫ (P.kleisli T).inl (Y := Kleisli.mk T Z)) :
    kleisliArrow (f ≫ m.app (P.sum Y Z)) =
      kleisliArrow (g.of ≫ m.app Y) ≫ (P.kleisli S.monad).inl (Y := Kleisli.mk S.monad Z) := by
  apply Kleisli.hom_ext
  have h : f = g.of ≫ T.map (P.inl (Y := Z)) :=
    (congrArg Kleisli.Hom.of e).trans (post_inl_of g)
  change f ≫ m.app (P.sum Y Z) = _
  rw [h, Category.assoc, m.toNatTrans.naturality, ← Category.assoc]
  exact (post_inl_of (kleisliArrow (g.of ≫ m.app Y))).symm

theorem vacuousMap_guarded (m : T ⟶ S.monad) :
    MonadGuardedness.Preserves P (vacuousMonad P T).guard S.guard m := by
  intro X Y Z f hf
  obtain ⟨g, e⟩ := hf
  have h := factor_map m f g e
  exact Eq.mpr (congrArg (S.guard.guarded (Y := Kleisli.mk S.monad Y) (Z := Kleisli.mk S.monad Z)) h)
    (S.guard.trivial (kleisliArrow (g.of ≫ m.app Y)))

private theorem iterate_factor {K : Type u} [Category.{v} K] {Q : Coproducts K}
    {G : Guardedness Q} (F : G.Fixpoints) {X Y : K} {f : X ⟶ Q.sum Y X}
    (hf : G.guarded f) (g : X ⟶ Y) (h : f = g ≫ Q.inl) : F.iterate f hf = g := by
  let q := F.iterate f hf
  have e : f ≫ Q.desc (𝟙 Y) q = q := F.fixpoint f hf
  rw [h, Category.assoc, Q.inl_desc, Category.comp_id] at e
  exact e.symm

theorem vacuousMap_iterates (m : T ⟶ S.monad) {X Y : C} (f : X ⟶ T.obj (P.sum Y X))
    (hf : (vacuousMonad P T).guard.guarded (kleisliArrow f)) :
    ((vacuousMonad P T).iteration.iterate (kleisliArrow f) hf).of ≫ m.app Y =
      (S.iteration.iterate (kleisliArrow (f ≫ m.app (P.sum Y X))) (vacuousMap_guarded m f hf)).of := by
  have factored := hf
  obtain ⟨g, e⟩ := factored
  have r := iterate_factor (vacuousMonad P T).iteration.toFixpoints hf g e
  have s := iterate_factor S.iteration.toFixpoints (vacuousMap_guarded m f hf)
    (kleisliArrow (g.of ≫ m.app Y)) (factor_map m f g e)
  exact (congrArg (fun z => z.of ≫ m.app Y) r).trans (congrArg Kleisli.Hom.of s).symm

theorem identityMap_unique (f : GuardedElgotMonadHom P (guardedIdentity P) S) :
    f.hom = identityMonadMap S.monad := by
  apply MonadHom.ext
  funext X
  have h := f.hom.app_η X
  change 𝟙 X ≫ f.hom.app X = S.monad.η.app X at h
  exact (Category.id_comp _).symm.trans h

/-- Total guards let a loop recurse immediately even with arbitrary return type. -/
theorem divergent_at (T : GuardedElgotMonad P) (h : T.IsElgot) (X Y : C) :
    Nonempty (X ⟶ T.monad.obj Y) := by
  let f : Kleisli.mk T.monad X ⟶ (P.kleisli T.monad).sum (Kleisli.mk T.monad Y) (Kleisli.mk T.monad X) :=
    (P.kleisli T.monad).inr
  exact ⟨(T.iteration.iterate f (h f)).of⟩

end Silmaril.Calco2019.Proofs
