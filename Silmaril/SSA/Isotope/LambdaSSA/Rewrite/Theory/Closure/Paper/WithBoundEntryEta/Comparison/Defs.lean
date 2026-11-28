module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Destructure.Defs

/-! # Entry-let and once-bound CFG η

The positive entry grammar permits effectful unary initializers and
case analysis on constructor values. Local rows may be arbitrary
constructor-branch regions, including recursion.
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Comparison

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Entry syntax for which typed unary entry-let and the native case-value
conversion suffice to push the re-entry continuation through the entry. -/
inductive SequencedEntry : VCtx τ → Region Φ → LCtx τ → Prop where
  | br {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {a : Tm Φ} {A : τ}
      (hi : At L i A) (ha : Tm.BranchValue Γ a A) : SequencedEntry Γ (.br i a) L
  | let₁ {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {A : τ} {r : Region Φ}
      (ha : Tm.HasType Γ a A) (hr : SequencedEntry (A :: Γ) r L) :
      SequencedEntry Γ (.let₁ a r) L
  | case {Γ : VCtx τ} {L : LCtx τ} {e : Tm Φ} {A B : τ} {l r : Region Φ}
      (he : Tm.BranchValue Γ e (Silmaril.coprod A B))
      (hl : SequencedEntry (A :: Γ) l L) (hr : SequencedEntry (B :: Γ) r L) :
      SequencedEntry Γ (.case e l r) L

namespace DestructureFixture

open SequencingObstruction (Instruction)

/-- A sum selects a local label, and its Unit arm first evaluates a call. -/
def sumEntry : Region Instruction :=
  .case (.var 0) (.let₁ (.op .tick (.var 0)) (.br 0 (.var 0))) (.br 1 (.var 0))

end DestructureFixture

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Comparison
