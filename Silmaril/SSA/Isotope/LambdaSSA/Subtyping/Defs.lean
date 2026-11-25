module

public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

/-! # Proof-relevant subtyping for λSSA expressions and regions -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Subtyping

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ]
  {Φ : Type v} [HasTy Φ τ]

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
inductive Tm.HasType : VCtx τ → LambdaSSA.Tm Φ → τ → Type _ where
  | var : At Γ i A → HasType Γ (.var i) A
  | op : HasType Γ a (instrSrc f) → HasType Γ (.op f a) (instrTrg f)
  | let₁ : HasType Γ a A → HasType (A :: Γ) b B → HasType Γ (.let₁ a b) B
  | pair : HasType Γ a A → HasType Γ b B → HasType Γ (.pair a b) (Silmaril.product A B)
  | unit : HasType Γ .unit Silmaril.unit
  | let₂ : HasType Γ a (Silmaril.product A B) →
      HasType (B :: A :: Γ) b C → HasType Γ (.let₂ a b) C
  | inl : HasType Γ a A → HasType Γ (.inl a) (Silmaril.coprod A B)
  | inr : HasType Γ b B → HasType Γ (.inr b) (Silmaril.coprod A B)
  | case : HasType Γ a (Silmaril.coprod A B) →
      HasType (A :: Γ) l C → HasType (B :: Γ) r C → HasType Γ (.case a l r) C
  | abort : HasType Γ a Silmaril.empty → HasType Γ (.abort a) A
  | sub : HasType Γ a A → Silmaril.Isotope.Subty A B → HasType Γ a B

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
inductive Region.HasType : VCtx τ → LambdaSSA.Region Φ → LCtx τ → Type _ where
  | br : At L ℓ A → Tm.HasType Γ a A → HasType Γ (.br ℓ a) L
  | case : Tm.HasType Γ a (Silmaril.coprod A B) →
      HasType (A :: Γ) l L → HasType (B :: Γ) r L → HasType Γ (.case a l r) L
  | let₁ : Tm.HasType Γ a A → HasType (A :: Γ) r L → HasType Γ (.let₁ a r) L
  | let₂ : Tm.HasType Γ a (Silmaril.product A B) →
      HasType (B :: A :: Γ) r L → HasType Γ (.let₂ a r) L
  | cfg {entry : LambdaSSA.Region Φ} {n : Nat}
      {blocks : Fin n → LambdaSSA.Region Φ} (R : Fin n → τ) :
      HasType Γ entry (List.ofFn R ++ L) →
      (∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
      HasType Γ (.cfg entry n blocks) L

/-- Rename variables while retaining every coercion witness. -/
def Tm.HasType.rename {Γ Δ : LambdaSSA.VCtx τ} {a : LambdaSSA.Tm Φ} {A : τ}
    {ρ : Nat → Nat} (hρ : LambdaSSA.Ren Γ Δ ρ) :
    Tm.HasType Γ a A → Tm.HasType Δ (a.rename ρ) A
  | .var h => .var (hρ h)
  | .op h => .op (h.rename hρ)
  | .let₁ ha hb => .let₁ (ha.rename hρ) (hb.rename (hρ.lift _))
  | .pair ha hb => .pair (ha.rename hρ) (hb.rename hρ)
  | .unit => .unit
  | .let₂ ha hb => .let₂ (ha.rename hρ) (hb.rename ((hρ.lift _).lift _))
  | .inl h => .inl (h.rename hρ)
  | .inr h => .inr (h.rename hρ)
  | .case he hl hr => .case (he.rename hρ)
      (hl.rename (hρ.lift _)) (hr.rename (hρ.lift _))
  | .abort h => .abort (h.rename hρ)
  | .sub h hAB => .sub (h.rename hρ) hAB

/-- Rename a region and its block typing derivations. -/
def Region.HasType.renameVars {Γ Δ : LambdaSSA.VCtx τ}
    {r : LambdaSSA.Region Φ} {L : LambdaSSA.LCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) :
    Region.HasType Γ r L → Region.HasType Δ (r.renameVars ρ) L
  | .br h ha => .br h (ha.rename hρ)
  | .case he hl hr => .case (he.rename hρ)
      (hl.renameVars (hρ.lift _)) (hr.renameVars (hρ.lift _))
  | .let₁ ha hr => .let₁ (ha.rename hρ) (hr.renameVars (hρ.lift _))
  | .let₂ ha hr => .let₂ (ha.rename hρ) (hr.renameVars ((hρ.lift _).lift _))
  | .cfg R he hb => .cfg R (he.renameVars hρ)
      (fun i => (hb i).renameVars (hρ.lift _))

end Silmaril.Isotope.LambdaSSA.Subtyping
