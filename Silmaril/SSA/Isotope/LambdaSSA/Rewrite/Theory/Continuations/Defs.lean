module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Substitution.Defs

/-! # Typed regions and equivalent continuation families -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Exact region typing with constructor-valued arguments at every branch.
The computations in let bindings and case scrutinees retain ordinary typing. -/
inductive ValueBranches : VCtx τ → Region Φ → LCtx τ → Prop where
  | br (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A) :
      ValueBranches Γ (.br ℓ a) L
  | let₁ (ha : Tm.HasType Γ a A) (hr : ValueBranches (A :: Γ) r L) :
      ValueBranches Γ (.let₁ a r) L
  | let₂ (ha : Tm.HasType Γ a (Silmaril.product A B)) (hr : ValueBranches (B :: A :: Γ) r L) :
      ValueBranches Γ (.let₂ a r) L
  | case (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : ValueBranches (A :: Γ) l L) (hr : ValueBranches (B :: Γ) r L) :
      ValueBranches Γ (.case a l r) L
  | cfg (R : Fin n → τ) (he : ValueBranches Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
      ValueBranches Γ (.cfg entry n blocks) L

/-- Pointwise equivalence of typed continuation families at the same exit interface. -/
@[expose] def LSubst.Equivalent (Γ : VCtx τ) (L K : LCtx τ) (σ σ' : Nat → Region Φ) : Prop :=
  ∀ ⦃ℓ A⦄, At L ℓ A → RewriteEquiv (A :: Γ) (σ ℓ) (σ' ℓ) K

/-- Attach one CFG block per exit of the entry. The continuations can reach
the final exits and do not refer back to these local block labels. -/
@[expose] def linkExits (r : Region Φ) (L : LCtx τ) (σ : Nat → Region Φ) : Region Φ :=
  .cfg r L.length (fun i => (σ i).renameLabels (fun j => L.length + j))

end Silmaril.Isotope.LambdaSSA.Region
