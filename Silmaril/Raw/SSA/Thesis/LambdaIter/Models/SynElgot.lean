module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.SynIteration
public import Silmaril.Semantics.Categories.Thms

/-!
# Syntactic λiter iteration in Mathlib’s coproduct vocabulary

The canonical isomorphism between the syntactic and chosen coproducts
transports fixpoint, naturality and codiagonal. The Elgot category theorem
assumes finite coproducts. The uniformity result uses the pure-arrow
subcategory, which still needs Cartesian and Freyd structure.
-/

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit false

namespace Silmaril.Thesis.LambdaIter

open LocallyNameless CategoryTheory CategoryTheory.Limits

universe u

namespace Syn.SynCat

variable {S : Sig.{u}}

/-- The canonical isomorphism between the object-language coproduct and
Mathlib's chosen binary coproduct in the syntactic category. -/
noncomputable def copIso (A B : SynCat S) : cop A B ≅ A ⨿ B := by
  let comparison := (isColimitBinaryCofan A B).coconePointUniqueUpToIso (coprodIsCoprod A B)
  exact comparison

@[simp] theorem injl_copIso_hom (A B : SynCat S) :
    injl A B ≫ (copIso A B).hom = coprod.inl := by
  simpa [copIso] using (isColimitBinaryCofan A B).comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod A B) ⟨WalkingPair.left⟩

@[simp] theorem injr_copIso_hom (A B : SynCat S) :
    injr A B ≫ (copIso A B).hom = coprod.inr := by
  simpa [copIso] using (isColimitBinaryCofan A B).comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod A B) ⟨WalkingPair.right⟩

@[simp] theorem coprod_inl_copIso_inv (A B : SynCat S) :
    (coprod.inl : A ⟶ A ⨿ B) ≫ (copIso A B).inv = injl A B := by
  rw [← injl_copIso_hom A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[simp] theorem coprod_inr_copIso_inv (A B : SynCat S) :
    (coprod.inr : B ⟶ A ⨿ B) ≫ (copIso A B).inv = injr A B := by
  rw [← injr_copIso_hom A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The two copairings agree across the isomorphism. -/
@[simp] theorem copIso_inv_desc {A B C : SynCat S} (l : A ⟶ C) (r : B ⟶ C) :
    (copIso A B).inv ≫ desc l r = coprod.desc l r := by
  rw [Iso.inv_comp_eq]
  have h := desc_uniq ((copIso A B).hom ≫ coprod.desc l r)
  rw [← Category.assoc, ← Category.assoc, injl_copIso_hom, injr_copIso_hom,
    coprod.inl_desc, coprod.inr_desc] at h
  exact h.symm

/-- Iteration on the syntactic category, phrased with Mathlib's chosen binary
coproduct.  This is exactly the operation that a `CategoryTheory.Iteration`
instance would carry; it is left as a plain definition, see the module
docstring. -/
noncomputable def iterate' {A B : SynCat S} (f : A ⟶ B ⨿ A) : A ⟶ B :=
  iterate (f ≫ (copIso B A).inv)

/-- **Fixpoint**, in the shape of `CategoryTheory.ElgotCategory.fixpoint`. -/
theorem iterate'_fixpoint {A B : SynCat S} (f : A ⟶ B ⨿ A) :
    iterate' f = f ≫ coprod.desc (𝟙 B) (iterate' f) := by
  conv_lhs => rw [iterate', iterate_fixpoint (f ≫ (copIso B A).inv)]
  rw [Category.assoc, copIso_inv_desc]
  rfl

/-- **Naturality**, in the shape of `CategoryTheory.ElgotCategory.naturality`. -/
theorem iterate'_naturality {A B C : SynCat S} (f : A ⟶ B ⨿ A) (g : B ⟶ C) :
    iterate' f ≫ g = iterate' (f ≫ coprod.map g (𝟙 A)) := by
  have key : (copIso B A).inv ≫ desc (g ≫ injl C A) (injr C A)
      = coprod.map g (𝟙 A) ≫ (copIso C A).inv := by
    rw [copIso_inv_desc]
    refine coprod.hom_ext ?_ ?_ <;> simp
  simp only [iterate']
  rw [iterate_naturality]
  simp only [Category.assoc]
  rw [key]

/-- **Codiagonal**, in the shape of `CategoryTheory.ElgotCategory.codiagonal`. -/
theorem iterate'_codiagonal {A B : SynCat S} (f : A ⟶ (B ⨿ A) ⨿ A) :
    iterate' (iterate' f) =
      iterate' (f ≫ coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A)) := by
  have key : (copIso (B ⨿ A) A).inv ≫
        (desc ((copIso B A).inv ≫ injl (cop B A) A) (injr (cop B A) A) ≫
          desc (𝟙 (cop B A)) (injr B A))
      = coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A) ≫ (copIso B A).inv := by
    rw [← Category.assoc, copIso_inv_desc]
    refine coprod.hom_ext ?_ ?_ <;>
      simp [injl_desc, injr_desc]
  simp only [iterate']
  rw [iterate_naturality, iterate_codiagonal]
  simp only [Category.assoc]
  rw [key]

/-- The iteration operator, packaged as a `CategoryTheory.Iteration`
structure.  A plain `def`, not an `instance`: see the module docstring. -/
@[reducible] noncomputable def iterationStructure (S : Sig.{u}) :
    Iteration (SynCat S) where
  iterate := iterate'

/-- Package the iteration laws for a supplied finite-coproduct structure.
The `SyntacticCategory.Thms` header constructs this structure from the empty
type and binary coproducts. -/
theorem elgotCategory_of_hasFiniteCoproducts (S : Sig.{u})
    [HasFiniteCoproducts (SynCat S)] :
    @ElgotCategory (SynCat S) _ _ (iterationStructure S) := by
  let _ : Iteration (SynCat S) := iterationStructure S
  exact
    { fixpoint := fun f => iterate'_fixpoint f
      naturality := fun f g => iterate'_naturality f g
      codiagonal := fun f => iterate'_codiagonal f }

end Syn.SynCat

end Silmaril.Thesis.LambdaIter
