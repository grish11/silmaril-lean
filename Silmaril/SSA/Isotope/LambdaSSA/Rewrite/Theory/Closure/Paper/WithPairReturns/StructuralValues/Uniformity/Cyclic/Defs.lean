module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Thms

/-! # The exact guarded fold and its recursive blocks -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open Extension.Singleton (TypeCategory ofType sumCofan sumIso)
open Extension.Singleton.ValueCoproducts (exactCopair)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => Extension.Singleton.TypeCategory S
local notation "Obj" => ofType S

local infixr:65 " ⊕ₜ " => Silmaril.coprod
local notation "U" => (Silmaril.unit : τ)

/-- Put the retained summand first and the two copies of Unit together. -/
noncomputable def rotate (X Y Z : Q) : X ⨿ (Y ⨿ Z) ≅ Z ⨿ (X ⨿ Y) where
  hom := coprod.desc (coprod.inl ≫ coprod.inr) (coprod.desc (coprod.inr ≫ coprod.inr) coprod.inl)
  inv := coprod.desc (coprod.inr ≫ coprod.inr) (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr))
  hom_inv_id := by
    apply coprod.hom_ext
    · simp
    · apply coprod.hom_ext <;> simp
  inv_hom_id := by
    apply coprod.hom_ext
    · simp
    · apply coprod.hom_ext <;> simp

noncomputable def swap (X Y : Q) : X ⨿ Y ≅ Y ⨿ X where
  hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl
  hom_inv_id := by apply coprod.hom_ext <;> simp
  inv_hom_id := by apply coprod.hom_ext <;> simp

/-- Fold the extra Unit onto the original Unit tag, preserving the whole other summand. -/
noncomputable def foldState (R : τ) : Obj (U ⊕ₜ (U ⊕ₜ R)) ⟶ Obj (U ⊕ₜ R) :=
  exactCopair S (sumCofan S U R).inl (𝟙 _)

noncomputable abbrev sourceIso (R : τ) : Obj (U ⊕ₜ (U ⊕ₜ R)) ≅ Obj R ⨿ (Obj U ⨿ Obj U) :=
  sumIso S U (U ⊕ₜ R) ≪≫ coprod.mapIso (Iso.refl _) (sumIso S U R) ≪≫ rotate S (Obj U) (Obj U) (Obj R)

noncomputable abbrev targetIso (R : τ) : Obj (U ⊕ₜ R) ≅ Obj R ⨿ Obj U :=
  sumIso S U R ≪≫ swap S (Obj U) (Obj R)

/-- Realize a block presentation as a feedback step at the exact state object. -/
noncomputable abbrev realize {A D B X : Q} (split : X ≅ A ⨿ D) (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    X ⟶ B ⨿ X :=
  split.hom ≫ d ≫ (coprod.associator B A D).hom ≫ coprod.map (𝟙 B) split.inv

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic
