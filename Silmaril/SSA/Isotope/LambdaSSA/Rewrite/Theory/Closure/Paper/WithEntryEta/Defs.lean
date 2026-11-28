module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Typed literal CFG η at arbitrary arity

The local interface is `List.ofFn R` and precedes the outward interface
`L` in the de Bruijn label context. The continuation at each in-scope
label re-enters the same table with its payload and weakens the old
blocks past that capture. This is the literal family in the written
CFG η and legacy `Region.Eqv.cfg_eq_ucfg`, including the outward-label
continuations. The legacy proof also uses a variant that forwards an
outward label directly at index `i - n` and proves it equal to the
literal family in the quotient.
[Written rule](https://github.com/imbrem/thesis/blob/198c67fae4240edf1bc19194cda63adedb0944cd/papers/isotope/denotational-semantics-of-ssa.tex#L2130-L2144) ·
[Printed η](https://github.com/imbrem/thesis/blob/198c67fae4240edf1bc19194cda63adedb0944cd/papers/isotope/denotational-semantics-of-ssa.tex#L2403-L2411) ·
[Legacy continuations](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/LSubst.lean#L571-L580) ·
[Legacy comparison of the two families](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/LSubst.lean#L669-L680) ·
[Legacy quotient equation](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Rewrite/Region/LSubst.lean#L682-L684)

This exact-typing slice uses `ValueBranches` for the entry and blocks.
The written and legacy typing rules allow any bottom-typed branch
argument. Constructor values give a structural purity witness in the
exact model. Let initializers and case scrutinees retain ordinary
exact typing, including effectful computations.
[Written typing](https://github.com/imbrem/thesis/blob/198c67fae4240edf1bc19194cda63adedb0944cd/papers/isotope/denotational-semantics-of-ssa.tex#L1361-L1386) ·
[Legacy typing](https://github.com/imbrem/debruijn-ssa/blob/316bd9a6511d165b5d1d0042956a72e0f5547091/DeBruijnSSA/BinSyntax/Typing/Region/Basic.lean#L40-L51)
-/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Substitute the typed re-entry family into the entry of a finite CFG. -/
inductive Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop where
  | reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
      {blocks : Fin n → Region Φ} (R : Fin n → τ)
      (he : ValueBranches Γ entry (List.ofFn R ++ L))
      (hb : ∀ i, ValueBranches (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
      Step Γ (.cfg entry n blocks) (entry.lsubst (cfgEntryContinuations blocks)) L

/-- The contextual region relation with the additional literal η rule. -/
abbrev Eqv := Extension.Eqv (Step (τ := τ) (Φ := Φ))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryEta
