module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.BranchNormalization.Defs

/-! # Once-bound CFG η at arbitrary arity

The seed uses ordinary exact region typing for the entry and blocks. Its
right side evaluates every entry branch argument once before applying
the literal re-entry family. The written and legacy region judgments
instead impose bottom typing on branch arguments. The constructor guard in
`WithEntryEta` is a sufficient structural witness in the exact calculus.
Here the special re-entry family also admits the literal form as a derived
law: its entry branch forwards the payload once, and the weakened blocks
cannot refer to that payload.
[Printed η](https://github.com/imbrem/thesis/blob/198c67fae4240edf1bc19194cda63adedb0944cd/papers/isotope/denotational-semantics-of-ssa.tex#L2403-L2411) ·
[Printed branch typing](https://github.com/imbrem/thesis/blob/198c67fae4240edf1bc19194cda63adedb0944cd/papers/isotope/denotational-semantics-of-ssa.tex#L1361-L1378) ·
[Legacy branch typing](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Typing/Region/Basic.lean#L40-L51) ·
[Legacy re-entry](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/LSubst.lean#L682-L684)
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Substitute the re-entry family after binding branch arguments. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
      {blocks : Fin n → Region Φ} (R : Fin n → τ)
      (he : HasType Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
      Step Γ (.cfg entry n blocks) (entry.bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L

/-- The typed contextual closure with once-bound η as its extra rule. -/
abbrev Eqv := Extension.Eqv (Step (τ := τ) (Φ := Φ))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta
