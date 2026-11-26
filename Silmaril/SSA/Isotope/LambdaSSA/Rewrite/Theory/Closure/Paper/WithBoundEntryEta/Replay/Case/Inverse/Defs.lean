module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Defs

/-! # Shared typed tables for inverse case hoisting -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay

open WithEntryLet (Site)
open Generators (weakenRows)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- At the selected case both arm tables are weakenings of one table typed
before either case payload. Both arm entries use the same local label
types. The outer constructors identify the exact value and label scopes
at the address. -/
inductive CommonTableAt : VCtx τ → LCtx τ → Site → Region Φ → Prop where
  | here {Γ : VCtx τ} {L : LCtx τ} {n : Nat} {A B : τ} {a : Tm Φ} {l r : Region Φ}
      {rows : Fin n → Region Φ} (R : Fin n → τ) (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : HasType (A :: Γ) l (List.ofFn R ++ L))
      (hr : HasType (B :: Γ) r (List.ofFn R ++ L))
      (hb : ∀ j, HasType (R j :: Γ) (rows j) (List.ofFn R ++ L)) :
      CommonTableAt Γ L .here (.case a (.cfg l n (weakenRows rows)) (.cfg r n (weakenRows rows)))
  | unaryBody {Γ : VCtx τ} {L : LCtx τ} {site : Site} {A : τ} {a : Tm Φ} {r : Region Φ}
      (ha : Tm.HasType Γ a A) (body : CommonTableAt (A :: Γ) L site r) :
      CommonTableAt Γ L (.unaryBody site) (.let₁ a r)
  | binaryBody {Γ : VCtx τ} {L : LCtx τ} {site : Site} {A B : τ} {a : Tm Φ} {r : Region Φ}
      (ha : Tm.HasType Γ a (Silmaril.product A B)) (body : CommonTableAt (B :: A :: Γ) L site r) :
      CommonTableAt Γ L (.binaryBody site) (.let₂ a r)
  | leftArm {Γ : VCtx τ} {L : LCtx τ} {site : Site} {A B : τ} {a : Tm Φ} {l r : Region Φ}
      (ha : Tm.HasType Γ a (Silmaril.coprod A B)) (left : CommonTableAt (A :: Γ) L site l)
      (right : HasType (B :: Γ) r L) : CommonTableAt Γ L (.leftArm site) (.case a l r)
  | rightArm {Γ : VCtx τ} {L : LCtx τ} {site : Site} {A B : τ} {a : Tm Φ} {l r : Region Φ}
      (ha : Tm.HasType Γ a (Silmaril.coprod A B)) (left : HasType (A :: Γ) l L)
      (right : CommonTableAt (B :: Γ) L site r) : CommonTableAt Γ L (.rightArm site) (.case a l r)
  | entry {Γ : VCtx τ} {L : LCtx τ} {site : Site} {n : Nat} {e : Region Φ} {rows : Fin n → Region Φ}
      (R : Fin n → τ) (entry : CommonTableAt Γ (List.ofFn R ++ L) site e)
      (hb : ∀ j, HasType (R j :: Γ) (rows j) (List.ofFn R ++ L)) :
      CommonTableAt Γ L (.entry site) (.cfg e n rows)
  | block {Γ : VCtx τ} {L : LCtx τ} {site : Site} {n : Nat} {e : Region Φ} {rows : Fin n → Region Φ}
      (R : Fin n → τ) (i : Fin n) (he : HasType Γ e (List.ofFn R ++ L))
      (hb : ∀ j, j ≠ i → HasType (R j :: Γ) (rows j) (List.ofFn R ++ L))
      (body : CommonTableAt (R i :: Γ) (List.ofFn R ++ L) site (rows i)) :
      CommonTableAt Γ L (.block i.val site) (.cfg e n rows)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.CaseReplay
