module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixTyped

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseReturns.BinaryFold
open Paper.WithCaseReturns.BinaryFold.MatrixBoundary.Binary
open Paper.BoundSimulation
open CfgEta.TypeCategory (returnRegion returnRegion_typed)

private theorem bitValue_typed (i : Fin 2) : Tm.BranchValue ([] : VCtx (Ty Empty)) (bitValue i) BitTy := by
  unfold bitValue
  split
  · exact .inl .unit
  · exact .inr .unit

theorem entry_typed (initial : Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary.PhaseState) :
    ValueBranches [] (entry initial) [PhaseTy, ExitTy] := by
  cases initial with
  | inl i => exact .br rfl (.inl (bitValue_typed i))
  | inr i => exact .br rfl (.inr (bitValue_typed i))

private theorem phaseValue_typed (initial : Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary.PhaseState) :
    Tm.BranchValue ([] : VCtx (Ty Empty)) (phaseValue initial) PhaseTy := by
  cases initial with
  | inl i => exact .inl (bitValue_typed i)
  | inr i => exact .inr (bitValue_typed i)

theorem entry_after_fold (initial : Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary.PhaseState) :
    Paper.WithCaseReturns.Eqv false ([] : VCtx (Ty Empty))
      ((entry initial).lsubst (boundLocalMap foldTerm))
      (.br 0 (bitValue (initial.elim id id))) [BitTy, ExitTy] := by
  let tail : Region Op := returnRegion (.var 0)
  let choose : Region Op := .case (.var 0) tail tail
  let arm : Tm.HasType [BitTy] (.var 0 : Tm Op) BitTy := .var rfl
  have hleft : ValueBranches [PhaseTy] (returnRegion (foldTerm (Φ := Op))) [BitTy] :=
    returnRegion_typed (fold_typed BitTy)
  have hright : ValueBranches [PhaseTy] choose [BitTy] :=
    .case (.var rfl) (returnRegion_typed (.var rfl)) (returnRegion_typed (.var rfl))
  have seed : Paper.WithCaseReturns.Eqv false [PhaseTy] (returnRegion (foldTerm (Φ := Op))) choose [BitTy] :=
    .extra hleft.hasType hright.hasType (.inr (.split arm arm .var .var))
  have weaken : Ren [BitTy] [BitTy, ExitTy] id := by
    intro i A hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  have subst : ∀ ⦃i A⦄, At [PhaseTy] i A → Tm.BranchValue [] (Tm.singleSubst (phaseValue initial) i) A := by
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact phaseValue_typed initial
    | succ i => simp [At] at hi
  have eq := (seed.renameLabels weaken).substVars subst
  change Paper.WithCaseReturns.Eqv false [] ((entry initial).lsubst (boundLocalMap foldTerm))
    (.case (phaseValue initial) tail tail) [BitTy, ExitTy] at eq
  have htail : ValueBranches [BitTy] tail [BitTy, ExitTy] :=
    .let₁ arm (.br rfl (.var rfl))
  have hbr : ValueBranches [BitTy] (.br 0 (.var 0) : Region Op) [BitTy, ExitTy] := .br rfl (.var rfl)
  refine eq.trans (.paper (.cfgEta (.native ?_)))
  cases initial with
  | inl i =>
    exact (SubstitutionEquiv.base (.caseInl (bitValue_typed i).hasType htail.hasType htail.hasType)).trans
      ((SubstitutionEquiv.letValue (bitValue_typed i) htail.hasType).trans
        (.letValue (bitValue_typed i) hbr.hasType))
  | inr i =>
    exact (SubstitutionEquiv.base (.caseInr (bitValue_typed i).hasType htail.hasType htail.hasType)).trans
      ((SubstitutionEquiv.letValue (bitValue_typed i) htail.hasType).trans
        (.letValue (bitValue_typed i) hbr.hasType))

theorem alternating_instance :
    ∃ (p q : Region Op) (hp : ValueBranches [PhaseTy] p [PhaseTy, ExitTy])
      (hq : ValueBranches [BitTy] q [BitTy, ExitTy]),
      stepArrow hp = alternatingStep round ∧ stepArrow hq = round ∧
      ∀ initial, FoldStep false [] (.cfg (entry initial) 1 (fun _ => p))
        (.cfg ((entry initial).lsubst (boundLocalMap foldTerm)) 1 (fun _ => q)) [ExitTy] := by
  obtain ⟨p, hp, eqp⟩ := exists_stepArrow (alternatingStep round)
  obtain ⟨q, hq, eqq⟩ := exists_stepArrow round
  refine ⟨p, q, hp, hq, eqp.symm, eqq.symm, fun initial => ?_⟩
  exact .simulate (entry_typed initial) hp hq (local_square false hp hq (by rw [← eqp, ← eqq]))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixTyped
