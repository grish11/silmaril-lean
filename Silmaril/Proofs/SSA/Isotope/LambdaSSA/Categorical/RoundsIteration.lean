module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Rounds.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.PhaseIteration

/-! # Unrolling in every Elgot Freyd category

The proof uses the fixpoint, naturality and codiagonal laws of the
computation category and uniformity along pure maps only: coproduct
injections of phase objects and the map that forgets the phase.
-/

public section

universe v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (roundsStep PhaseSystem)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [ElgotFreydCategory J]

section Cases

variable {A B : V} {T : C}

/-- Case analysis on a pure binary sum of phases. -/
noncomputable def dJ (u : J.obj A ⟶ T) (v : J.obj B ⟶ T) : J.obj (A ⨿ B) ⟶ T :=
  (PreservesColimitPair.iso J A B).inv ≫ coprod.desc u v

@[reassoc]
theorem inl_dJ (u : J.obj A ⟶ T) (v : J.obj B ⟶ T) : J.map coprod.inl ≫ dJ J u v = u := by
  have h : J.map (coprod.inl : A ⟶ A ⨿ B) = coprod.inl ≫ (PreservesColimitPair.iso J A B).hom := by
    rw [PreservesColimitPair.iso_hom, inl_coprodComparison]
  rw [dJ, h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inl_desc]

@[reassoc]
theorem inr_dJ (u : J.obj A ⟶ T) (v : J.obj B ⟶ T) : J.map coprod.inr ≫ dJ J u v = v := by
  have h : J.map (coprod.inr : B ⟶ A ⨿ B) = coprod.inr ≫ (PreservesColimitPair.iso J A B).hom := by
    rw [PreservesColimitPair.iso_hom, inr_coprodComparison]
  rw [dJ, h, Category.assoc, Iso.hom_inv_id_assoc, coprod.inr_desc]

theorem dJ_ext {f g : J.obj (A ⨿ B) ⟶ T}
    (hl : J.map coprod.inl ≫ f = J.map coprod.inl ≫ g)
    (hr : J.map coprod.inr ≫ f = J.map coprod.inr ≫ g) : f = g := by
  rw [← cancel_epi (PreservesColimitPair.iso J A B).hom]
  apply coprod.hom_ext
  · rw [PreservesColimitPair.iso_hom, inl_coprodComparison_assoc, inl_coprodComparison_assoc]
    exact hl
  · rw [PreservesColimitPair.iso_hom, inr_coprodComparison_assoc, inr_coprodComparison_assoc]
    exact hr

end Cases

variable (X : V)

/-- Phases of a pure state object: binary sums in the value category. -/
@[expose] noncomputable def phases : Nat → V
  | 0 => X
  | k + 1 => X ⨿ phases k

/-- The phase system of an Elgot Freyd category at a pure state object.
Its injections are pure, so the two uniformity fields are instances of
pure uniformity. -/
@[expose] noncomputable def system : PhaseSystem C where
  iter := iterate
  fixpoint := ElgotCategory.fixpoint
  naturality := ElgotCategory.naturality
  codiagonal := ElgotCategory.codiagonal
  obj k := J.obj (phases X k)
  inl _ := J.map coprod.inl
  inr _ := J.map coprod.inr
  desc _ := dJ J
  inl_desc _ _ u v := inl_dJ J u v
  inr_desc _ _ u v := inr_dJ J u v
  ext _ _ _ _ hl hr := dJ_ext J hl hr
  uniform_inl _ _ f g comm := ElgotFreydCategory.pure_uniformity J f g coprod.inl comm
  uniform_inr _ _ f g comm := ElgotFreydCategory.pure_uniformity J f g coprod.inr comm

/-- The fold of the phases is pure. -/
theorem fold_pure : ∀ k, ∃ m : phases X k ⟶ X, (system J X).fold k = J.map m
  | 0 => ⟨𝟙 X, (J.map_id X).symm⟩
  | k + 1 => by
    obtain ⟨m, hm⟩ := fold_pure k
    refine ⟨coprod.desc (𝟙 X) m, ?_⟩
    change dJ J (𝟙 (J.obj X)) ((system J X).fold k) =
      J.map (coprod.desc (𝟙 X) m : X ⨿ phases X k ⟶ X)
    rw [hm]
    apply dJ_ext J
    · exact (inl_dJ J _ _).trans (((J.map_comp _ _).symm.trans
        (congrArg J.map (coprod.inl_desc _ _))).trans (J.map_id X)).symm
    · exact (inr_dJ J _ _).trans ((J.map_comp _ _).symm.trans
        (congrArg J.map (coprod.inr_desc _ _))).symm

/-- The loop on any number of rounds of a step on a pure state object is
the loop on one round. -/
theorem iterate_roundsStep {X : V} {Y : C} (h : J.obj X ⟶ Y ⨿ J.obj X) (n : Nat) :
    iterate (roundsStep h n) = iterate h := by
  obtain ⟨m, hm⟩ := fold_pure J X n
  refine PhaseIteration.iter_roundsStep_of_fold (system J X) h n (fun c square => ?_)
  rw [hm] at square ⊢
  exact ElgotFreydCategory.pure_uniformity J c h m square

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.RoundsIteration
