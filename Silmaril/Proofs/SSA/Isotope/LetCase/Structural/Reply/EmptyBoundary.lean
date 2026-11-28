module

public import Silmaril.SSA.Isotope.LetCase.Structural.Reply.Defs

public section

namespace Silmaril.Isotope.LetCase.Structural.Reply

open CategoryTheory
open LocallyNameless (Derivation Equiv Tm)
open LetIter.Semantics.Categorical (denote_let_abort)
open scoped LetSeq.StraightLine.Structural

variable {α Φ : Type} [HasTy Φ (Ty α)]

theorem empty_sequence_valid_proof {n : Nat} {β : BoundCtx (Ty α) n} {t : Tm Empty Φ n}
    (a : Derivation Φ Γ₀ β t .empty) (A : Ty α) :
    Valid (.abort (C := A) a) (.let₁ a (.abort (C := A) (.bv (ι := 0)))) := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central
    M instr _ _ _
  exact (denote_let_abort J M (Morphism.CaseIter.derivation a) A).symm

namespace EmptyBoundary

theorem unprovable_proof :
    ¬ Equiv false (Φ := signature.Instr) Γ₀ input
      (.abort (.op true .unit)) (.let₁ (.op true .unit) (.abort (.bv 0))) (.unit : Ty Empty) := by
  intro h
  have closed := h.instantiate
    (.unit : LocallyNameless.HasType signature.Instr Γ₀ (.nil : BoundCtx (Ty Empty) 0) .unit .unit) .unit
  exact LetIter.Semantics.Categorical.AbortCounterexample.exact_abortSequence_unprovable
    (Morphism.CaseIter.embed_equiv closed)

end EmptyBoundary

end Silmaril.Isotope.LetCase.Structural.Reply
