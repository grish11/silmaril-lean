module

public import Silmaril.SSA.Isotope.LetParIter.Institution.Defs
public import Silmaril.SSA.Isotope.LetParIter.Shared.Defs

/-! # Exact syntax and model restrictions of LetParIter

The sequential restriction keeps iteration and forgets parallel pairing. The
case-tier restriction keeps parallel pairing and forgets iteration. Both use
the same value interpretation, sequencing and instructions.
-/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Institution

open Parallel LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.Institution (InstrSig)

universe u v w

variable {τ ε : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν] {P : InstrSig τ ε}
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

/-- Include an exact LetIter derivation using the native embedding. -/
def Expr.ofLetIter {t : LetIter.LocallyNameless.Tm ν P.Instr n}
    (d : LetIter.LocallyNameless.Derivation P.Instr Γ β t A) : Expr P Γ β A :=
  ⟨LetParIter.embed t, LetParIter.derivation d⟩

/-- Include an exact case-tier derivation with the native widening. -/
def Expr.ofLetParCase {t : LetParCase.Tm ν P.Instr n}
    (d : Derivation P.Instr Γ β t A) : Expr P Γ β A :=
  ⟨LetParIter.ofLetParCase t, LetParIter.ofLetParCaseDerivation d⟩

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

/-- Evaluate the stored witness using the common parallel-tier interpreter. -/
def Model.evalShared (M : Model P) (a : Expr P Γ β A)
    (γ : CtxDen Γ) (ρ : BoundDen β) : M.Carrier (TyDen A) :=
  letI := M.instructions
  LetParIter.interpret (ε := ε) M.pairing a.typing γ ρ

/-- Evaluate exact LetIter typing in the underlying sequential model. -/
def Model.evalLetIter (M : Model P) {t : LetIter.LocallyNameless.Tm ν P.Instr n}
    (d : LetIter.LocallyNameless.Derivation P.Instr Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) : M.Carrier (TyDen A) :=
  letI := M.instructions
  LetIter.ProofRelevant.Semantics.denote (ε := ε) (LetParIter.nativeTyping d) γ ρ

variable (τ) in
/-- The case tier uses the native sum and empty equivalences and has no loop clause. -/
def caseControl (m : Type v → Type v) : Control .case (TyDen (τ := τ)) m where
  sum _ := TypeModel.coprodEquiv
  zero _ := TypeModel.emptyEquiv.trans
    ⟨Empty.elim, PEmpty.elim, (fun e => nomatch e), (fun e => nomatch e)⟩
  loop h := nomatch h

/-- Evaluate in the shared native case-tier evaluator with the retained pairing.
Environments expose the same values through the case evaluator's lookup interface. -/
def Model.evalLetParCase (M : Model P) {t : LetParCase.Tm ν P.Instr n}
    (d : Derivation P.Instr Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) : M.Carrier (TyDen A) :=
  letI := M.instructions
  letI := LetParIter.nativeProductModel (τ := τ)
  letI := LetParIter.nativeUnitModel (τ := τ)
  d.denote (TyDen (τ := τ)) ⟨denoteInstr (ε := ε)⟩ (fun x y => M.pairing.pair x y)
    (caseControl τ M.Carrier) (fun x _ h => CtxDen.lookup γ x h) (BoundDen.get ρ)

end Silmaril.Isotope.LetParIter.Institution
