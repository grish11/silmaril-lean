module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Obstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CaseOperand.Thms

/-! # Default Paper separates the closed constructor-known request operands -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryOperandSeparation

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (caseOperand CaseOperandBeta)
open Paper.WithCaseBind.BitQuery.RequestTree.Readback.Obstruction
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

private theorem packed_relation_ne (label b : Bool) :
    ¬ Paper.Extension.Eqv Paper.WithComputedCallReturns.Step [U]
      (source label b).packExits (target label b).packExits [packedExitType Exits] := by
  have left : Tm.BranchValue [Bit, U] (.inl (.var 0) : Tm signature.Instr) (packedExitType Exits) :=
    .inl (.var (i := 0) rfl)
  exact Paper.BoundSimulation.Obstruction.PairSequencing.term_case_operand_ne
    (fun _ => .inl (.inl .unit)) (.inl .unit) (constructorBit_value b .unit) left

theorem packed_ne (label b : Bool) : sourcePacked label b ≠ targetPacked label b := by
  intro eq
  have native := (Paper.TypeCategory.ofRegion_eq_iff
    (source_typed label b).packExits (target_typed label b).packExits).mp eq
  exact packed_relation_ne label b (.paper native)

theorem packed_ne_with_call_sequencing (label b : Bool) :
    Paper.Extension.Singleton.ofRegion Paper.WithComputedCallReturns.Step (source_typed label b).packExits ≠
      Paper.Extension.Singleton.ofRegion Paper.WithComputedCallReturns.Step (target_typed label b).packExits := by
  intro eq
  exact packed_relation_ne label b ((Paper.Extension.Singleton.ofRegion_eq_iff _ _ _).mp eq)

theorem case_operand_beta_fails : ¬ CaseOperandBeta := by
  intro beta
  have left : ValueBranches [Bit, U] (.br 0 (.var 0) : Region signature.Instr) Exits :=
    .br rfl (.var (i := 0) rfl)
  have right : ValueBranches [Bit, U] (.br 1 (.var 0) : Region signature.Instr) Exits :=
    .br rfl (.var (i := 0) rfl)
  let θ := Tm.consSubst (.unit : Tm signature.Instr) Tm.var
  have hθ : ∀ i A, At [U] i A → Tm.BranchValue [U] (θ i) A := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .unit
    | succ i => simp [At] at hi
  have eq : Paper.Eqv [U] (source false false) (target false false) Exits :=
    (beta false false left right).substVars (θ := θ) (fun _ _ hi => hθ _ _ hi)
  have packed := Paper.Eqv.lsubstPost eq (source_typed false false) (target_typed false false)
    (fun _ _ hi => (packExits_valueFamily (Φ := signature.Instr) [U] Exits hi).hasType)
  exact packed_ne false false ((Paper.TypeCategory.ofRegion_eq_iff _ _).mpr packed)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryOperandSeparation
