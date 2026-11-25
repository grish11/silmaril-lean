module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Defs

/-! # Composition of native continuation classes -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K P Q : LCtx τ}

theorem continuationIdentity_compose (f : ContinuationHom (Φ := Φ) Γ L K) :
    ContinuationHom.compose (ContinuationHom.identity Γ L) f = f := by
  induction f using Quotient.inductionOn with
  | _ σ =>
      change Quotient.mk _ (ContinuationFamily.compose (ContinuationFamily.identity Γ L) σ) = Quotient.mk _ σ
      exact congrArg (Quotient.mk _) (Subtype.ext (compLSubst_id_left σ.val))

theorem continuationCompose_identity (f : ContinuationHom (Φ := Φ) Γ L K) :
    ContinuationHom.compose f (ContinuationHom.identity Γ K) = f := by
  induction f using Quotient.inductionOn with
  | _ σ =>
      change Quotient.mk _ (ContinuationFamily.compose σ (ContinuationFamily.identity Γ K)) = Quotient.mk _ σ
      exact congrArg (Quotient.mk _) (Subtype.ext (compLSubst_id_right σ.val))

theorem continuationCompose_assoc (f : ContinuationHom (Φ := Φ) Γ L K)
    (g : ContinuationHom (Φ := Φ) Γ K P) (h : ContinuationHom (Φ := Φ) Γ P Q) :
    ContinuationHom.compose (ContinuationHom.compose f g) h = ContinuationHom.compose f (ContinuationHom.compose g h) := by
  induction f, g, h using Quotient.inductionOn₃ with
  | _ σ υ ω =>
      change Quotient.mk _ (ContinuationFamily.compose (ContinuationFamily.compose σ υ) ω) =
        Quotient.mk _ (ContinuationFamily.compose σ (ContinuationFamily.compose υ ω))
      exact congrArg (Quotient.mk _) (Subtype.ext (compLSubst_assoc σ.val υ.val ω.val))

theorem bindBranchArguments_equiv {r : Region Φ} (hr : ValueBranches Γ r L) :
    SubstitutionEquiv Γ r r.bindBranchArguments L := by
  induction hr with
  | br hℓ ha => exact .symm (.letValue ha (.br hℓ (.var rfl)))
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
