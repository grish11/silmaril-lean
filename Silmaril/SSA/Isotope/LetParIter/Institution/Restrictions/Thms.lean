module

public import Silmaril.SSA.Isotope.LetParIter.Institution.Restrictions.Defs
public import Silmaril.SSA.Isotope.LetParIter.Institution.Thms
public import Silmaril.SSA.Isotope.LetParIter.Thms

/-! # Exact fragment satisfaction and soundness of native equations -/

public section

namespace Silmaril.Isotope.LetParIter.Institution

open LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.Institution (InstrSig)

universe u v w

variable {τ ε : Type u} [TypeFormers τ] [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {P : InstrSig τ ε}
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- Agreement with the shared evaluator fixes the exact witness, environments,
type interpretation, instructions, iteration and pairing. The parent theorem
uses a lawful monad and a chosen iteration operation. Equality between distinct
typing witnesses requires a separate argument. -/
theorem Model.evalShared_eq_eval (M : Model P) (a : Expr P Γ β A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.evalShared a γ ρ = M.eval a γ ρ :=
  letI := M.instructions
  LetParIter.interpret_eq_denote M.pairing a.typing γ ρ

/-- Truth can also be computed by evaluating both stored witnesses in the common tier. -/
theorem satisfaction_iff_evalShared (M : Model P) (s : Sentence P ν) :
    Sat M s ↔ ∀ (γ : CtxDen s.Γ) (ρ : BoundDen s.β),
      M.evalShared s.lhs γ ρ = M.evalShared s.rhs γ ρ := by
  simp only [Sat, Model.evalShared_eq_eval]

/-- On the embedded exact fragment, evaluation is native LetIter evaluation. -/
theorem Model.eval_ofLetIter (M : Model P) {t : LetIter.LocallyNameless.Tm ν P.Instr n}
    (d : LetIter.LocallyNameless.Derivation P.Instr Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.eval (Expr.ofLetIter d) γ ρ = M.evalLetIter d γ ρ :=
  letI := M.instructions
  LetParIter.denote_embed M.pairing d γ ρ

/-- Truth on embedded exact equations is truth in the native sequential restriction. -/
theorem satisfaction_ofLetIter (M : Model P) {t t' : LetIter.LocallyNameless.Tm ν P.Instr n}
    (d : LetIter.LocallyNameless.Derivation P.Instr Γ β t A)
    (d' : LetIter.LocallyNameless.Derivation P.Instr Γ β t' A) :
    Sat M ⟨Γ, n, β, A, Expr.ofLetIter d, Expr.ofLetIter d'⟩ ↔
      ∀ (γ : CtxDen Γ) (ρ : BoundDen β), M.evalLetIter d γ ρ = M.evalLetIter d' γ ρ := by
  simp only [Sat, Model.eval_ofLetIter]

/-- The native equational theory is sound in these models by the separate
native soundness theorem. The satisfaction condition itself compares evaluations
and is independent of the derivation of an equation. -/
theorem satisfaction_of_equiv (M : Model P) (s : Sentence P ν)
    (h : LetParIter.Equiv (⊥ : ε) s.Γ s.lhs.typing s.rhs.typing) : Sat M s :=
  letI := M.instructions
  fun γ ρ => LetParIter.sound M.pairing h γ ρ

end Silmaril.Isotope.LetParIter.Institution
