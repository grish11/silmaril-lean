module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Thms
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.ContinuationLaws
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.EquivalentContinuations

/-! # Continuation congruence for typed regions with constructor-valued branches -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem ValueBranches.hasType {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) : HasType Γ r L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.valueBranches_typed hr

/-- Equivalent continuations can replace the labels of any typed region whose
branch arguments are constructor values. Continuation bodies may be arbitrary. -/
theorem ValueBranches.lsubst_equivalent {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ σ' : Nat → Region Φ} (h : LSubst.Equivalent Γ L K σ σ') :
    RewriteEquiv Γ (r.lsubst σ) (r.lsubst σ') K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.lsubst_equivalent hr h

/-- Composition of σ with υ respects pointwise continuation equivalence
when υ forwards branches and σ' has constructor-valued branch arguments. -/
theorem LSubst.Equivalent.comp {Γ : VCtx τ} {L K P : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : LSubst.Equivalent Γ L K σ σ') (hυ : LSubst.Equivalent Γ K P υ υ')
    (hforward : LSubst.Forwards Γ K P υ)
    (hvalues : ∀ ⦃ℓ A⦄, At L ℓ A → ValueBranches (A :: Γ) (σ' ℓ) K) :
    LSubst.Equivalent Γ L P (compLSubst σ υ) (compLSubst σ' υ') :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.equivalentComp hσ hυ hforward hvalues

/-- The CFG representation of composition respects arbitrary equivalent
typed entries and continuation bodies, including effectful branch arguments. -/
theorem RewriteEquiv.linkExits {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {σ σ' : Nat → Region Φ} (hs : LSubst.Equivalent Γ L K σ σ') :
    RewriteEquiv Γ (r.linkExits L σ) (s.linkExits L σ') K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.rewriteEquiv_linkExits h hs

/-- Connecting typed continuations by a CFG preserves the exact exit interface. -/
theorem HasType.linkExits {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    HasType Γ (r.linkExits L σ) K :=
  ((RewriteEquiv.refl hr).linkExits (fun _ _ hℓ => RewriteEquiv.refl (hσ hℓ))).typed.1

end Silmaril.Isotope.LambdaSSA.Region
