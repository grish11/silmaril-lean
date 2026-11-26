module

public import Silmaril.SSA.Isotope.Institution.Adapters.Iteration.Thms
public import Silmaril.SSA.Isotope.Institution.Adapters.Powerset.Thms
public import Silmaril.SSA.Isotope.Institution.Relational.Inclusions.Thms
import Silmaril.SSA.Isotope.Parallel.Hierarchy.Thms

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Proofs

open CategoryTheory Semantics
open Parallel (Derivation)
open Parallel.Institution (Equation)
open LetParIter.Institution (Expr)

universe u

variable {τ ε ν : Type u} [TypeFormers τ] [DecidableEq ν]
  {S : InstrSig τ ε} {Γ : Ctx ν τ}

theorem seqCase_sentence_commutes (φ : Relational.LetSeq.Sentence S Γ) :
    Powerset.ofLetCase (Relational.seqCaseSentence φ) = (Powerset.ofLetSeq φ).ofLetPar := by
  rw [Relational.seqCaseSentence_eq]
  let equation (l r : (a : LetParCase.Tm ν S.Instr φ.1.depth) ×
      Derivation S.Instr Γ φ.1.bound a φ.1.result) : Equation S .case Γ :=
    ⟨φ.1.depth, φ.1.bound, φ.1.result, l.1, r.1, l.2, r.2⟩
  exact congrArg₂ equation (Parallel.Hierarchy.seqCaseDerivation_commutes φ.2.1.2)
    (Parallel.Hierarchy.seqCaseDerivation_commutes φ.2.2.2)

theorem caseIter_sentence_commutes (φ : Relational.LetCase.Sentence S Γ) :
    Iteration.ofLetIter (Relational.caseIterSentence φ) =
      Iteration.ofLetParCase (Powerset.ofLetCase φ) := by
  rw [Relational.caseIterSentence_eq]
  let equation (l r : (a : LetParIter.Tm ν S.Instr φ.1.depth) ×
      Derivation S.Instr Γ φ.1.bound a φ.1.result) : LetParIter.Institution.Sentence S ν :=
    ⟨Γ, φ.1.depth, φ.1.bound, φ.1.result, ⟨l.1, l.2⟩, ⟨r.1, r.2⟩⟩
  exact congrArg₂ equation (Parallel.Hierarchy.caseIterDerivation_commutes φ.2.1.2)
    (Parallel.Hierarchy.caseIterDerivation_commutes φ.2.2.2)

end Silmaril.Isotope.Institution.Adapters.Proofs
