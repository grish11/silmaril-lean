module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Typed equations for substitution into arbitrary continuations -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Extend the native rewrite theory with pure let β for arbitrary region
bodies and elimination of CFGs whose entry targets only outward exits. -/
inductive SubstitutionEquiv : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | base : RewriteEquiv Γ r s L → SubstitutionEquiv Γ r s L
  | symm : SubstitutionEquiv Γ r s L → SubstitutionEquiv Γ s r L
  | trans : SubstitutionEquiv Γ r s L → SubstitutionEquiv Γ s t L → SubstitutionEquiv Γ r t L
  | let₁ (ha : Tm.HasType Γ a A) (hr : SubstitutionEquiv (A :: Γ) r s L) :
      SubstitutionEquiv Γ (.let₁ a r) (.let₁ a s) L
  | let₂ (ha : Tm.HasType Γ a (Silmaril.product A B)) (hr : SubstitutionEquiv (B :: A :: Γ) r s L) :
      SubstitutionEquiv Γ (.let₂ a r) (.let₂ a s) L
  | case (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : SubstitutionEquiv (A :: Γ) l l' L) (hr : SubstitutionEquiv (B :: Γ) r r' L) :
      SubstitutionEquiv Γ (.case a l r) (.case a l' r') L
  | cfg (R : Fin n → τ) (he : SubstitutionEquiv Γ entry entry' (List.ofFn R ++ L))
      (hb : ∀ i, SubstitutionEquiv (R i :: Γ) (blocks i) (blocks' i) (List.ofFn R ++ L)) :
      SubstitutionEquiv Γ (.cfg entry n blocks) (.cfg entry' n blocks') L
  | letValue (ha : Tm.BranchValue Γ a A) (hr : HasType (A :: Γ) r L) :
      SubstitutionEquiv Γ (.let₁ a r) (r.substVars (Tm.singleSubst a)) L
  | cfgOutward (R : Fin (n + 1) → τ) (hr : HasType Γ r L)
      (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
      SubstitutionEquiv Γ (.cfg (r.renameLabels (fun j => n + 1 + j)) (n + 1) blocks) r L

end Silmaril.Isotope.LambdaSSA.Region
