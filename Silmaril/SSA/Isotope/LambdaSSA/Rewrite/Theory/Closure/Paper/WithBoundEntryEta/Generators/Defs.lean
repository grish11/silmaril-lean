module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Defs

/-! # Local generators for once-bound CFG η

The binder moves use exact typing. The case generator keeps the
discriminator in case position. The nested generator wires the outward
exits of the inner table to the outer re-entry family and preserves
the inner labels.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators

open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Weaken every row past one new outer capture, below its local payload. -/
abbrev weakenRows {n : Nat} (bs : Fin n → Region Φ) : Fin n → Region Φ :=
  fun j => (bs j).renameVars (lift Nat.succ)

/-- The two entry-let schemas with exact typing for all regions. -/
inductive EntryLetStep : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | unary {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A : τ} {a : Tm Φ} {r : Region Φ}
      {bs : Fin n → Region Φ} (R : Fin n → τ)
      (ha : Tm.HasType Γ a A) (hr : HasType (A :: Γ) r (List.ofFn R ++ L))
      (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
      EntryLetStep Γ (.cfg (.let₁ a r) n bs) (.let₁ a (.cfg r n (weakenRows bs))) L
  | binary {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {r : Region Φ}
      {bs : Fin n → Region Φ} (R : Fin n → τ)
      (ha : Tm.HasType Γ a (Silmaril.product A B))
      (hr : HasType (B :: A :: Γ) r (List.ofFn R ++ L))
      (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
      EntryLetStep Γ (.cfg (.let₂ a r) n bs) (.let₂ a (.cfg r n (weakenRows (weakenRows bs)))) L

/-- The proposed join of both entry-let moves and the #4152 guarded bind. -/
abbrev Candidate := WithCaseBind.JoinedStep (EntryLetStep (τ := τ) (Φ := Φ))

/-- One structural equation for each form of CFG entry. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | entryLet {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} :
      EntryLetStep Γ r s L → Step Γ r s L
  | branch {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
      (hi : At L i A) (ha : Tm.HasType Γ a A) :
      Step Γ (.br i a) (.let₁ a (.br i (.var 0))) L
  | caseEntry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
      {bs : Fin n → Region Φ} (R : Fin n → τ)
      (ha : Tm.HasType Γ a (Silmaril.coprod A B))
      (hl : HasType (A :: Γ) l (List.ofFn R ++ L))
      (hr : HasType (B :: Γ) r (List.ofFn R ++ L))
      (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
      Step Γ (.cfg (.case a l r) n bs)
        (.case a (.cfg l n (weakenRows bs)) (.cfg r n (weakenRows bs))) L
  | nested {m n : Nat} {Γ : VCtx τ} {L : LCtx τ} {e : Region Φ}
      {inner : Fin m → Region Φ} {outer : Fin n → Region Φ} (S : Fin m → τ) (R : Fin n → τ)
      (he : HasType Γ e (List.ofFn S ++ (List.ofFn R ++ L)))
      (hi : ∀ j, HasType (S j :: Γ) (inner j) (List.ofFn S ++ (List.ofFn R ++ L)))
      (ho : ∀ j, HasType (R j :: Γ) (outer j) (List.ofFn R ++ L)) :
      Step Γ (.cfg (.cfg e m inner) n outer)
        (.cfg (e.lsubst (liftLSubstN m (cfgEntryContinuations outer))) m
          (fun j => (inner j).lsubst (liftLSubstVars (liftLSubstN m (cfgEntryContinuations outer))))) L

abbrev Eqv := Extension.Eqv (Step (τ := τ) (Φ := Φ))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators
