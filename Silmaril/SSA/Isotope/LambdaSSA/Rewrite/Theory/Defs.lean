module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Defs
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Continuation

/-! # Typed let and CFG equations

The entry equations are included along with let substitution into a branch
and case selection. Equations are indexed by their exact input and exit
contexts and closed under the region constructors.
-/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The typed theory of CFG entry, branch let substitution, and case selection. -/
inductive RewriteEquiv : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | entry : CfgEquiv Γ r s L → RewriteEquiv Γ r s L
  | symm : RewriteEquiv Γ r s L → RewriteEquiv Γ s r L
  | trans : RewriteEquiv Γ r s L → RewriteEquiv Γ s t L → RewriteEquiv Γ r t L
  | let₁ (ha : Tm.HasType Γ a A) (hr : RewriteEquiv (A :: Γ) r s L) :
      RewriteEquiv Γ (.let₁ a r) (.let₁ a s) L
  | let₂ (ha : Tm.HasType Γ a (Silmaril.product A B)) (hr : RewriteEquiv (B :: A :: Γ) r s L) :
      RewriteEquiv Γ (.let₂ a r) (.let₂ a s) L
  | case (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : RewriteEquiv (A :: Γ) l l' L) (hr : RewriteEquiv (B :: Γ) r r' L) :
      RewriteEquiv Γ (.case a l r) (.case a l' r') L
  | cfg (R : Fin n → τ) (he : RewriteEquiv Γ entry entry' (List.ofFn R ++ L))
      (hb : ∀ i, RewriteEquiv (R i :: Γ) (blocks i) (blocks' i) (List.ofFn R ++ L)) :
      RewriteEquiv Γ (.cfg entry n blocks) (.cfg entry' n blocks') L
  | letBr (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue (A :: Γ) b B) (hℓ : At L ℓ B) :
      RewriteEquiv Γ (.let₁ a (.br ℓ b))
        (.br ℓ (b.subst (Tm.singleSubst a))) L
  | caseInl (ha : Tm.HasType Γ a A) (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
      RewriteEquiv Γ (.case (.inl a) l r) (.let₁ a l) L
  | caseInr (hb : Tm.HasType Γ b B) (hl : HasType (A :: Γ) l L) (hr : HasType (B :: Γ) r L) :
      RewriteEquiv Γ (.case (.inr b) l r) (.let₁ b r) L

end Silmaril.Isotope.LambdaSSA.Region
