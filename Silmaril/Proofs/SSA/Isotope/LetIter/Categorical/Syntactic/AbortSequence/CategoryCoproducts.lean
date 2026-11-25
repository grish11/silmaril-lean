module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms

/-! # Coproducts of the abort-extended LetIter computation category -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedCoproductProofs

open CategoryTheory CategoryTheory.Limits
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

/-- The initial computation object remains initial after projecting the arrows. -/
noncomputable def repairedProjection_initial :
    IsInitial ((P).obj (⊥_ (SynCat S))) :=
  IsInitial.ofUniqueHom (fun X => (P).map (initial.to X.as)) (by
    intro X f
    obtain ⟨f, rfl⟩ := (P).map_surjective (Y := X.as) f
    exact congrArg (fun g => (P).map g) (initial.hom_ext _ _))

/-- The projected coproduct injections still jointly determine arrows. -/
theorem repairedProjection_coprod_hom_ext {X Y : SynCat S}
    {Z : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    {f g : (P).obj (X ⨿ Y) ⟶ Z}
    (hl : (P).map (coprod.inl : X ⟶ X ⨿ Y) ≫ f = (P).map coprod.inl ≫ g)
    (hr : (P).map (coprod.inr : Y ⟶ X ⨿ Y) ≫ f = (P).map coprod.inr ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := (P).map_surjective (Y := Z.as) f
  obtain ⟨g, rfl⟩ := (P).map_surjective (Y := Z.as) g
  simp only [← Functor.map_comp] at hl hr
  apply (repairedProjection_map_eq_iff pe _ _).mpr
  simpa only [← coprod.desc_comp, coprod.desc_inl_inr, Category.id_comp] using
    repairedHomClass_coprodDesc_congr pe
      ((repairedProjection_map_eq_iff pe _ _).mp hl) ((repairedProjection_map_eq_iff pe _ _).mp hr)

/-- The projected coproduct cocone has its expected universal property. -/
noncomputable def repairedProjection_coprodIsColimit (X Y : SynCat S) :
    IsColimit (BinaryCofan.mk
      ((P).map (coprod.inl : X ⟶ X ⨿ Y)) ((P).map (coprod.inr : Y ⟶ X ⨿ Y))) := by
  refine BinaryCofan.isColimitMk (fun s =>
    (P).map (coprod.desc ((P).preimage (Y := s.pt.as) s.inl) ((P).preimage (Y := s.pt.as) s.inr))) ?_ ?_ ?_
  · intro s
    rw [← (P).map_comp, coprod.inl_desc, (P).map_preimage]
  · intro s
    rw [← (P).map_comp, coprod.inr_desc, (P).map_preimage]
  · intro s m hl hr
    apply repairedProjection_coprod_hom_ext pe
    · rw [hl, ← (P).map_comp, coprod.inl_desc, (P).map_preimage]
    · rw [hr, ← (P).map_comp, coprod.inr_desc, (P).map_preimage]

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedCoproductProofs
