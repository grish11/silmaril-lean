module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution

/-! # Categorical renaming of native expressions -/

public section

universe v₁ v₂ u₁ u₂ u v

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

variable (J : V ⥤ C) [DistributiveFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

/-- A typed renaming transports a native expression denotation by its pure
environment map, characterized on variable lookups. -/
theorem Denotes.rename {Γ : VCtx τ} {a : Tm Φ} {A : τ} {ha : Tm.HasType Γ a A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} (d : Denotes J M ha f)
    {Δ : VCtx τ} {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) {p : ctxObj M Δ ⟶ ctxObj M Γ}
    (hp : ∀ ⦃i B⦄ (h : At Γ i B), p ≫ lookup M i h = lookup M (ρ i) (hρ h)) :
    Denotes J M (ha.rename hρ) (J.map p ≫ f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.denotes_rename J M d hρ hp

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
