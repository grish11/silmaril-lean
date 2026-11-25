module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ContinuationCategory

/-! # The syntactic category of typed continuations with value branches -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

theorem ContinuationHom.identity_compose {L K : LCtx τ} (f : ContinuationHom (Φ := Φ) Γ L K) :
    (ContinuationHom.identity Γ L).compose f = f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.continuationIdentity_compose f

theorem ContinuationHom.compose_identity {L K : LCtx τ} (f : ContinuationHom (Φ := Φ) Γ L K) :
    f.compose (ContinuationHom.identity Γ K) = f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.continuationCompose_identity f

theorem ContinuationHom.compose_assoc {L K P Q : LCtx τ}
    (f : ContinuationHom (Φ := Φ) Γ L K) (g : ContinuationHom (Φ := Φ) Γ K P)
    (h : ContinuationHom (Φ := Φ) Γ P Q) :
    (f.compose g).compose h = f.compose (g.compose h) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.continuationCompose_assoc f g h

/-- Continuations with value branches compose by native label substitution.
They may contain arbitrary typed computations before each branch. -/
instance continuationCategory : Category.{v} (ContinuationContext Φ Γ) where
  Hom X Y := ContinuationHom (Φ := Φ) Γ X.labels Y.labels
  id X := ContinuationHom.identity Γ X.labels
  comp := ContinuationHom.compose
  id_comp := ContinuationHom.identity_compose
  comp_id := ContinuationHom.compose_identity
  assoc := ContinuationHom.compose_assoc

/-- A typed continuation family represents an arrow between its exact exit interfaces. -/
@[expose] def ContinuationFamily.toHom {X Y : ContinuationContext Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels) : X ⟶ Y :=
  Quotient.mk _ σ

/-- Normalize the arguments of an arbitrary typed family once, before
placing each continuation in the category. -/
@[expose] def ContinuationFamily.ofTyped {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.HasType Γ L K σ) : ContinuationFamily (Φ := Φ) Γ L K :=
  ⟨fun i => (σ i).bindBranchArguments, fun _ _ hi => (hσ hi).bindBranchArguments⟩

theorem ContinuationFamily.toHom_eq_iff {X Y : ContinuationContext Φ Γ}
    {σ υ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels} :
    σ.toHom (X := X) (Y := Y) = υ.toHom (X := X) (Y := Y) ↔
      ∀ ⦃ℓ A⦄, At X.labels ℓ A → SubstitutionEquiv (A :: Γ) (σ.val ℓ) (υ.val ℓ) Y.labels :=
  Quotient.eq

@[simp] theorem ContinuationFamily.identity_toHom (X : ContinuationContext Φ Γ) :
    (ContinuationFamily.identity Γ X.labels).toHom (X := X) (Y := X) = 𝟙 X :=
  rfl

@[simp] theorem ContinuationFamily.compose_toHom {X Y Z : ContinuationContext Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels)
    (υ : ContinuationFamily (Φ := Φ) Γ Y.labels Z.labels) :
    (σ.compose υ).toHom (X := X) (Y := Z) =
      σ.toHom (X := X) (Y := Y) ≫ υ.toHom (X := Y) (Y := Z) :=
  rfl

/-- Normalizing a family that already has value branches gives the same arrow. -/
theorem ContinuationFamily.ofTyped_toHom {X Y : ContinuationContext Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels) :
    (ContinuationFamily.ofTyped (σ := σ.val) (fun _ _ hi => (σ.property hi).hasType)).toHom
      (X := X) (Y := Y) = σ.toHom (X := X) (Y := Y) := by
  apply ContinuationFamily.toHom_eq_iff.mpr
  intro ℓ A hi
  exact (Proofs.SSA.Isotope.LambdaSSA.Rewrite.bindBranchArguments_equiv (σ.property hi)).symm

end Silmaril.Isotope.LambdaSSA.Region
