module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Bekic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Blocks.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.BlockIteration

/-! # Default Paper is a block system at every exact sum -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBlocks

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Semantics.Categorical (BlockSystem)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (R P : τ)

set_option backward.isDefEq.respectTransparency false

/-- The two injections are constructor values, so guarded iteration is
uniform along them. -/
@[expose] noncomputable def blockSystem : BlockSystem (Paper.TypeCategory (τ := τ) Φ) where
  iter := iterate
  fixpoint := iterate_fixpoint
  naturality := iterate_naturality
  codiagonal := iterate_codiagonal
  left := ofType R
  right := ofType P
  sum := ofType (Silmaril.coprod R P)
  inl := sumInl R P
  inr := sumInr R P
  desc u v := (sumIso R P).hom ≫ coprod.desc u v
  inl_desc u v := by
    unfold sumInl
    rw [Category.assoc, Iso.inv_hom_id_assoc, coprod.inl_desc]
  inr_desc u v := by
    unfold sumInr
    rw [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]
  ext hl hr := SingletonPhases.sum_ext R P hl hr
  uniform_inl f g comm := SingletonPhases.uniform_inl R P _ f g comm
  uniform_inr f g comm := SingletonPhases.uniform_inr R P _ f g comm

variable {Y : τ} (r : ofType (Φ := Φ) R ⟶ (ofType Y ⨿ ofType R) ⨿ ofType P)
  (c : ofType (Φ := Φ) P ⟶ (ofType Y ⨿ ofType R) ⨿ ofType P)

theorem bekic :
    sumInl R P ≫ iterate (blockStep R P r c) = iterate (r ≫ coprod.desc (𝟙 _) (iterate c)) ∧
    sumInr R P ≫ iterate (blockStep R P r c) =
      iterate c ≫ coprod.desc (𝟙 _) (sumInl R P ≫ iterate (blockStep R P r c)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.BlockIteration.bekic (blockSystem R P) r c

/-- A map out of an exact sum is the copair of its two restrictions. -/
theorem sum_decomp {T : τ} (x : ofType (Φ := Φ) (Silmaril.coprod R P) ⟶ ofType T) :
    x = (sumIso R P).hom ≫ coprod.desc (sumInl R P ≫ x) (sumInr R P ≫ x) :=
  SingletonPhases.sum_ext R P ((blockSystem R P).inl_desc _ _).symm ((blockSystem R P).inr_desc _ _).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBlocks
