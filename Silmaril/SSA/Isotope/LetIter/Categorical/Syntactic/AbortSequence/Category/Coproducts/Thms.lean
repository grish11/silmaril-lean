module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryCoproducts

/-! # Finite coproducts and comparison for the LetIter computation quotient -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

/-- The initial computation object remains initial after projection. -/
noncomputable def repairedProjection_initial :
    IsInitial ((P).obj (⊥_ (SynCat S))) :=
  RepairedCoproductProofs.repairedProjection_initial pe

/-- The projected coproduct injections jointly determine arrows. -/
theorem repairedProjection_coprod_hom_ext {X Y : SynCat S}
    {Z : RepairedSynCat (τ := τ) (Φ := Φ) pe}
    {f g : (P).obj (X ⨿ Y) ⟶ Z}
    (hl : (P).map (coprod.inl : X ⟶ X ⨿ Y) ≫ f = (P).map coprod.inl ≫ g)
    (hr : (P).map (coprod.inr : Y ⟶ X ⨿ Y) ≫ f = (P).map coprod.inr ≫ g) : f = g :=
  RepairedCoproductProofs.repairedProjection_coprod_hom_ext pe hl hr

/-- The projected exact coproduct cocone is a coproduct in the computation quotient. -/
noncomputable def repairedProjection_coprodIsColimit (X Y : SynCat S) :
    IsColimit (BinaryCofan.mk
      ((P).map (coprod.inl : X ⟶ X ⨿ Y)) ((P).map (coprod.inr : Y ⟶ X ⨿ Y))) :=
  RepairedCoproductProofs.repairedProjection_coprodIsColimit pe X Y

/-- Finite computation coproducts exist in the repaired category. -/
instance repairedFiniteCoproducts : HasFiniteCoproducts (RepairedSynCat (τ := τ) (Φ := Φ) pe) := by
  have : HasInitial (RepairedSynCat (τ := τ) (Φ := Φ) pe) :=
    (repairedProjection_initial pe).hasInitial
  have : ∀ {X Y : RepairedSynCat (τ := τ) (Φ := Φ) pe}, HasColimit (pair X Y) :=
    fun {X Y} => ⟨⟨_, repairedProjection_coprodIsColimit pe X.as Y.as⟩⟩
  have : HasBinaryCoproducts (RepairedSynCat (τ := τ) (Φ := Φ) pe) :=
    hasBinaryCoproducts_of_hasColimit_pair (RepairedSynCat (τ := τ) (Φ := Φ) pe)
  exact hasFiniteCoproducts_of_has_binary_and_initial

/-- The quotient's chosen coproduct agrees with the projected exact coproduct. -/
noncomputable def repairedProjectionCoprodIso (X Y : SynCat S) :
    (P).obj (X ⨿ Y) ≅ (P).obj X ⨿ (P).obj Y :=
  (repairedProjection_coprodIsColimit pe X Y).coconePointUniqueUpToIso
    (colimit.isColimit (pair ((P).obj X) ((P).obj Y)))

theorem repairedProjection_coprodIso_inl (X Y : SynCat S) :
    (P).map (coprod.inl : X ⟶ X ⨿ Y) ≫ (repairedProjectionCoprodIso pe X Y).hom =
      coprod.inl := by
  exact (repairedProjection_coprodIsColimit pe X Y).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair ((P).obj X) ((P).obj Y))) ⟨WalkingPair.left⟩

theorem repairedProjection_coprodIso_inr (X Y : SynCat S) :
    (P).map (coprod.inr : Y ⟶ X ⨿ Y) ≫ (repairedProjectionCoprodIso pe X Y).hom =
      coprod.inr := by
  exact (repairedProjection_coprodIsColimit pe X Y).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair ((P).obj X) ((P).obj Y))) ⟨WalkingPair.right⟩

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
