module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CaseReturns

/-! # A syntactic observation of the selected open terminal -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement.NativeReplay
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Env EnvTy Result)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer   (TermObservation SameWith extension_same unary_fusion_same)
open scoped Paper.BoundSimulation.Obstruction Observer.CanonicalUnit

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local instance : HasEff signature.Instr Bool := signature.hasEff

private def observation : TermObservation (α := Empty) signature.Instr where
  pairLet := true
  pairLetCall := some (fun
    | .emit b => b
    | .ask _ => false)
  callResult
    | .emit _ => some .unit
    | .ask true => some (.inl (.inr .unit))
    | .ask false => some (.inr (.inr .unit))
  callResult_typed p _ _ h := by
    cases p with
    | emit => cases Option.some.inj h; exact .unit
    | ask b =>
      cases b <;> cases Option.some.inj h
      · exact .inr (.inr .unit)
      · exact .inl (.inr .unit)

private def terminalEnv : Env :=
  fun _ => .pair (.pair (.pair (.pair .unit (.inl .unit)) (.inr .unit)) .unit) (.inl .unit)

private theorem terminalEnv_typed : EnvTy [TerminalInput] terminalEnv := by
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .pair (.pair (.pair (.pair .unit (.inl .unit)) (.inr .unit)) .unit) (.inl .unit)
  | succ i => simp [At] at hi

theorem selected_terminal_ne (pos : Position Exits) :
    ¬ Paper.Extension.Eqv Seed [TerminalInput]
      (terminal pos (.read 1)).elaborate.val (terminal pos (Finite.Expr.quote 2 (fun env => env 1))).elaborate.val
      Exits := by
  intro h
  have obs := joined_same (observation := observation) h terminalEnv terminalEnv_typed
  change Result.fault = .jump pos.1 (.inr .unit) at obs
  cases obs

private theorem unitEnv_typed : EnvTy [(Ty.unit : Ty Empty)] (fun _ => .unit) := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

theorem selected_closed_ne :
    ¬ Paper.Extension.Eqv Seed [Ty.unit] direct.selected.elaborate.val table.selected.elaborate.val Exits := by
  intro h
  have obs := joined_same (observation := observation) h (fun _ => .unit) unitEnv_typed
  change Result.fault = .jump 1 (.inr .unit) at obs
  cases obs

private theorem caseUnarySeed_same {Γ L : List (Ty Empty)} {r s : Region signature.Instr}
    (step : Paper.WithCaseAndUnaryReturns.JoinedStep false Γ r s L) : SameWith observation Γ r s :=
  step.elim projectionUnitSeed_same (fun returns => returns.elim (unary_fusion_same rfl) (caseReturnSeed_same rfl))

theorem selected_packed_caseUnary_ne :
    ¬ Paper.Extension.Eqv (Paper.WithCaseAndUnaryReturns.JoinedStep false) [Ty.unit]
      direct.selected.elaborate.val.packExits table.selected.elaborate.val.packExits [packedExitType Exits] := by
  intro h
  have obs := extension_same caseUnarySeed_same h (fun _ => .unit) unitEnv_typed
  change Result.fault = .jump 0 (.inr (.inl (.inr .unit))) at obs
  cases obs

theorem prefixed_test_ne :
    ¬ Paper.Extension.Eqv Seed [Bit] (prefixedTest (.seq .input .input)).elaborate.val
      (prefixedTest .input).elaborate.val Exits := by
  intro h
  have bitTyped : EnvTy [Bit] (fun _ => .inl .unit) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl .unit
    | succ i => simp [At] at hi
  have obs := joined_same (observation := observation) h (fun _ => .inl .unit) bitTyped
  change Result.fault = .jump 0 (.inl .unit) at obs
  cases obs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
