module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Defs

/-! # Pruning constructor tests after substituting an already-bound payload -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA

universe v

variable {Φ : Type v}

/-- The known injection of a previously evaluated sum payload. -/
inductive CaseTag where
  | inl
  | inr

def CaseTag.inject : CaseTag → Tm Φ → Tm Φ
  | .inl => Tm.inl
  | .inr => Tm.inr

def CaseTag.select (tag : CaseTag) (left right : Region Φ) : Region Φ :=
  match tag with
  | .inl => left
  | .inr => right

/-- The payload at index zero also supplies the original tagged sum at
index one. Older captured variables shift down by one. -/
def Tm.restoreTag (tag : CaseTag) : Nat → Tm Φ
  | 0 => .var 0
  | 1 => tag.inject (.var 0)
  | n + 2 => .var (n + 1)

/-- Prune tests of injected variables. The selected case payload is
substituted using the usual lifted de Bruijn substitution. Other case
scrutinees and let initializers are retained in their written order. -/
inductive Region.PruneConstructorTests : Region Φ → Region Φ → Prop where
  | keep (r : Region Φ) : PruneConstructorTests r r
  | let₁ {a : Tm Φ} {r s : Region Φ} :
      PruneConstructorTests r s → PruneConstructorTests (.let₁ a r) (.let₁ a s)
  | case {a : Tm Φ} {l r l' r' : Region Φ} :
      PruneConstructorTests l l' → PruneConstructorTests r r' →
        PruneConstructorTests (.case a l r) (.case a l' r')
  | inl {i : Nat} {l r s : Region Φ} :
      PruneConstructorTests (l.substVars (Tm.singleSubst (.var i))) s →
        PruneConstructorTests (.case (.inl (.var i)) l r) s
  | inr {i : Nat} {l r s : Region Φ} :
      PruneConstructorTests (r.substVars (Tm.singleSubst (.var i))) s →
        PruneConstructorTests (.case (.inr (.var i)) l r) s

end Silmaril.Isotope.LambdaSSA
