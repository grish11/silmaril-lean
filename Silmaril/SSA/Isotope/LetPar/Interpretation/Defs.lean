module

public import Silmaril.SSA.Isotope.LetPar.Defs
public import Silmaril.Raw.SSA.Isotope.Semantics.Model

/-! Monadic interpretation with an explicitly supplied parallel operation. -/

@[expose] public section

namespace Silmaril.Isotope.Parallel

open Semantics

universe u v w q

/-- The operation used by the interpreter. A lawful parallel-pairing model can pass
its pairing directly. -/
abbrev ParOp (m : Type v → Type v) :=
  {A B : Type v} → m A → m B → m (A × B)

/-- Model data for the optional control forms of a tier. -/
structure Control (tier : Tier) {τ : Type u} [CaseTypes tier τ]
    (D : τ → Type v) (m : Type v → Type v) where
  sum (h : tier.HasCase) (A B : τ) : D (CaseTypes.sum h A B) ≃ Sum (D A) (D B)
  zero (h : tier.HasCase) : D (CaseTypes.zero h) ≃ PEmpty.{v + 1}
  loop : tier.HasIter → ∀ {A B : τ}, (D A → m (Sum (D B) (D A))) → D A → m (D B)

def Control.seq {τ : Type u} (D : τ → Type v) (m : Type v → Type v) : Control .seq D m where
  sum h := False.elim (h rfl)
  zero h := False.elim (h rfl)
  loop h := nomatch h

def Control.case {τ : Type u} [CoproductTypeFormers τ]
    (D : τ → Type v) [CoproductModel D] [EmptyModel D] (m : Type v → Type v) :
    Control .case D m where
  sum _ := CoproductModel.coprodEquiv
  zero _ := EmptyModel.emptyEquiv
  loop h := nomatch h

namespace Derivation

variable {tier : Tier} {τ : Type u} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  (D : τ → Type v) [ProductModel D] [UnitModel D]
  {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
  {m : Type v → Type v} [Monad m]
  (M : InstructionModel D Φ m) (P : ParOp m) (C : Control tier D m)

/-- Evaluate ordinary forms with monadic sequencing. For `par`, feed both branch
computations the original environment and pass their results to the parallel operation. -/
def denote : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm tier ν Φ n} → {A : τ} → Derivation Φ Γ β t A →
    FreeEnv D Γ → BoundEnv D β → m (D A)
  | _, _, _, _, _, .fv h, γ, _ => pure (γ _ _ h)
  | _, _, _, _, _, .bv, _, ρ => pure (ρ _)
  | _, _, _, _, _, .op ha, γ, ρ => denote ha γ ρ >>= M.eval _
  | _, _, _, _, _, .let₁ ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a => denote hb γ (ρ.snoc a)
  | _, _, _, _, _, .unit, _, _ => pure ((UnitModel.unitEquiv (D := D)).symm PUnit.unit)
  | _, _, _, _, _, .pair ha hb, γ, ρ =>
      denote ha γ ρ >>= fun a =>
      denote hb γ ρ >>= fun b =>
      pure ((ProductModel.productEquiv (D := D) _ _).symm (a, b))
  | _, _, _, _, _, .let₂ ha hb, γ, ρ =>
      denote ha γ ρ >>= fun ab =>
      let p := ProductModel.productEquiv (D := D) _ _ ab
      denote hb γ ((ρ.snoc p.1).snoc p.2)
  | _, _, _, .inl h _, _, .inl ha, γ, ρ =>
      denote ha γ ρ >>= fun a => pure ((C.sum h _ _).symm (.inl a))
  | _, _, _, .inr h _, _, .inr hb, γ, ρ =>
      denote hb γ ρ >>= fun b => pure ((C.sum h _ _).symm (.inr b))
  | _, _, _, .case h _ _ _, _, .case he hl hr, γ, ρ =>
      denote he γ ρ >>= fun e =>
      match C.sum h _ _ e with
      | .inl a => denote hl γ (ρ.snoc a)
      | .inr b => denote hr γ (ρ.snoc b)
  | _, _, _, .abort h _, _, .abort ha, γ, ρ =>
      denote ha γ ρ >>= fun z => PEmpty.elim (C.zero h z)
  | _, _, _, .iter h _ _, _, .iter ha hb, γ, ρ =>
      denote ha γ ρ >>= C.loop h (fun a =>
        denote hb γ (ρ.snoc a) >>= fun b => pure (C.sum (Tier.iterHasCase h) _ _ b))
  | _, _, _, _, _, .par ha hb, γ, ρ =>
      P (denote ha γ ρ) (denote hb γ ρ) >>= fun p =>
        pure ((ProductModel.productEquiv (D := D) _ _).symm p)

end Derivation

end Silmaril.Isotope.Parallel
