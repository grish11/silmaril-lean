module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheorySubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Forwarding

/-! # Substitution congruence for typed λSSA rewrites -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Applying the same simultaneous constructor-value substitution to both
sides of an equation preserves the typed rewrite relation. -/
theorem RewriteEquiv.substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {σ : Nat → Tm Φ}
    (hσ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (σ i) A) :
    RewriteEquiv Δ (r.substVars σ) (s.substVars σ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.rewriteEquiv_substVars h hσ

/-- Native label substitution preserves equations when all replacements
are typed constructor-valued branches. -/
theorem RewriteEquiv.lsubst {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.Forwards Γ L K σ) :
    RewriteEquiv Γ (r.lsubst σ) (s.lsubst σ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.rewriteEquiv_lsubst h hσ

/-- A typed label renaming is a forwarding substitution that retains the
original argument at every exit. -/
theorem RewriteEquiv.renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) {ρ : Nat → Nat} (hρ : SSA.Ren L K ρ) :
    RewriteEquiv Γ (r.renameLabels ρ) (s.renameLabels ρ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.rewriteEquiv_renameLabels h hρ

end Silmaril.Isotope.LambdaSSA.Region
