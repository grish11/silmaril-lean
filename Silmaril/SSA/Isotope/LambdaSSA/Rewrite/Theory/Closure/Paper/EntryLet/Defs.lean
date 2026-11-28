module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs

/-! # Literal CFG entry substitution at a fixed arity -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- The arity-`n` form of literal CFG η. Each typed local label is interpreted
by re-entering the same table at that label. -/
def EntryEta (τ : Type u) [TypeFormers τ] (Φ : Type v) [HasTy Φ τ] (n : Nat) : Prop :=
  ∀ {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ} {blocks : Fin n → Region Φ}
      (R : Fin n → τ),
    ValueBranches Γ entry (List.ofFn R ++ L) →
    (∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) →
    Eqv Γ (.cfg entry n blocks) (entry.lsubst (cfgEntryContinuations blocks)) L

end Silmaril.Isotope.LambdaSSA.Region.Paper
