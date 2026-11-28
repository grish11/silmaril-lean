module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg WordOp model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def spec : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 2]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .ne
  limit := 42
  guardRhs := some (.arg 2)
  exitSlot := 2
  exitOrigin := some (.output 1 0)

private def plan : Plan 3 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardIndex := 0
  comparison := .ne
  limit := 42
  guardOperand := .bank 2
  exitSlot := 2
  exitProducer := some 1

private def targets : Checked.Phi.Targets := (lowerBank plan.graph, Generic.lower plan.graph)
private theorem checked : checkPlan 3 spec = some plan := by cbv
private theorem accepted : lowerChecked 3 spec = some targets := by cbv

example : lowerChecked 3 { spec with guardRhs := some (.arg 3) } = none := by cbv
example : lowerChecked 3 { spec with guardRhs := some (.output 1 1) } = none := by cbv

example : plan.guardOperands.addresses = [.output 0 0, .arg 5] := by cbv

example : (bankHeader plan.graph).ops[2]? = some (.binary (.cmp .ne) (.node 2) (.node 0) (.arg 5)) :=
  guard_compare_operand plan

example : (targets.1.block? 0 1).map (·.term) =
    some (.cond (.node 2) 1 [.node 0, .arg 4, .node 1] 2 [.node 1]) := by cbv

-- Inspect the actual emitted CFG in either dynamic operand mode. Both
-- branches read from the scheduled header.
private def headerWires (cfg : Region (Primitive WordOp)) (right : Nat) : Prop :=
  match cfg with
    | .cfg _ n blocks =>
      if inside : 0 < n then
        match blocks ⟨0, inside⟩ with
        | .let₂ _ (.let₂ _ (.let₂ _ body)) =>
          match body with
          | .let₁ _ (.let₁ _ (.let₁ (.op (.apply .ne) (.pair (.var lhs) (.pair (.var rhs) .unit)))
              (.case (.var predicate) (.br 0 feedback) (.br 1 (.pair (.var result) .unit))))) =>
            (lhs, rhs, predicate, result) = (1, right, 0, 2) ∧
              feedback = .pair (.var 3) (.pair (.var 7) (.pair (.var 2) .unit))
          | _ => False
        | _ => False
      else False
    | _ => False

example : headerWires targets.2 3 := by cbv

private def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))
private def input := bank 0 1 5
private def spin := bank 1 0 5
private def mem := Memory.ofList 4 [29, 71, 53, 11]

-- The last activation compares next counter 3 with old slot 2's value 3,
-- even though the subtraction has already produced 2 for that slot.
private theorem nativeReturns :
    plan.graph.ReturnsAfter model input 2 (plan.graph.initial model input) (2 : Word) :=
  .backedge (next := bank 1 1 4) (by cbv)
    (.backedge (next := bank 2 1 3) (by cbv) (.exit (by cbv)))

example : ({ plan with guardOperand := .limit }).graph.evalBackedges model 2 input = none := by cbv
example : plan.rtlFuel 2 = 14 := rfl
example : ({ plan with guardOperand := .limit }).rtlFuel 2 = 17 := rfl

example : targets.1.runMain 14 0 (words input) mem = .returned [2] mem :=
  (runMain_fuel_iff plan input mem mem [2] 14).mpr ⟨2, (2 : Word), nativeReturns, by decide, rfl, rfl⟩

example : targets.1.runMain 14 0 (words input) mem = .returned [2] mem := by cbv
example : (targets.1.runMain 13 0 (words input) mem).returnedValues? = none := by cbv
example : targets.1.runMain 6 0 (words (bank 4 1 5)) mem = .returned [4] mem := by cbv

example : Generic.Fuel.run model (inputEnv model input) 3 targets.2 =
    some (0, Generic.packResult model (out := word) (2 : Word)) := by cbv

example : Eval (instruction model) (inputEnv model input) targets.2 mem 0
    (Generic.packResult model (out := word) (2 : Word)) mem :=
  (lambda_return_iff checked accepted _ _ _ _ _).mpr
    ⟨(2 : Word), (plan.graph.returns_iff_mem_denote model _ _).mp ⟨2, nativeReturns⟩, rfl, rfl, rfl⟩

private theorem spinUndefined (p : Plan 3) (entry : p.graph.initial model spin = spin)
    (step : p.graph.step model spin spin = .inr spin) :
    p.program.graph.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact p.graph.not_returns_of_backedge_invariant model spin value (· = spin) entry
    (fun old fixed => by
      subst old
      exact ⟨spin, step, rfl⟩)
    ((p.graph.returns_iff_mem_denote model _ _).mpr present)

example : ∀ returned final, ¬ targets.1.oracle 0 (words spin) mem returned final :=
  (no_finite_return_iff checked accepted _ _).1.mpr (spinUndefined plan (by cbv) (by cbv))

example : ∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin)
    targets.2 mem label payload final :=
  (no_finite_return_iff checked accepted _ _).2.mpr (spinUndefined plan (by cbv) (by cbv))

private def swap : InputPermutation 3 := Equiv.swap 0 1
private def mapped := plan.reindexInputs swap
private def reemitted : Checked.Phi.Targets := (lowerBank mapped.graph, Generic.lower mapped.graph)

example : lowerChecked 3 (spec.reindexInputs swap) = some reemitted := by cbv
example : bankHeader mapped.graph = bankHeader plan.graph := rfl
example : reemitted.1.runMain 14 0 (words (bank 1 0 5)) mem = .returned [2] mem := by cbv
example : Generic.Fuel.run model (inputEnv model (bank 1 0 5)) 3 reemitted.2 =
    some (0, Generic.packResult model (out := word) (2 : Word)) := by cbv

private def computedSpec : Spec := { spec with guardRhs := some (.output 1 0) }
private def computedPlan : Plan 3 := { plan with guardOperand := .computed ⟨1, by decide⟩ }
private def computedTargets : Checked.Phi.Targets :=
  (lowerBank computedPlan.graph, Generic.lower computedPlan.graph)

private theorem computedChecked : checkPlan 3 computedSpec = some computedPlan := by cbv
private theorem computedAccepted : lowerChecked 3 computedSpec = some computedTargets := by cbv

example : lowerChecked 3 { computedSpec with guardRhs := some (.output 2 0) } = none := by cbv
example : lowerChecked 3 { computedSpec with guardRhs := some (.output 1 1) } = none := by cbv
example : lowerChecked 3 { computedSpec with guardRhs := some (.output 0 0) } = none := by cbv

example : computedPlan.guardOperands.addresses = [.output 0 0, .output 1 0] := by cbv
example : (bankHeader computedPlan.graph).ops[2]? =
    some (.binary (.cmp .ne) (.node 2) (.node 0) (.node 1)) :=
  guard_compare_computed computedPlan ⟨1, by decide⟩ rfl
example : (computedTargets.1.block? 0 1).map (·.term) =
    some (.cond (.node 2) 1 [.node 0, .arg 4, .node 1] 2 [.node 1]) := by cbv
example : headerWires computedTargets.2 0 := by cbv

private def meet := bank 0 1 6

-- Compare 2 + 1 with 4 - 1. Reading old slot 2 instead would take feedback.
example : computedPlan.graph.step model meet (bank 2 1 4) = .inl (3 : Word) := by cbv
example : plan.graph.step model meet (bank 2 1 4) = .inr (bank 3 1 3) := by cbv

private theorem computedReturns :
    computedPlan.graph.ReturnsAfter model meet 2 (computedPlan.graph.initial model meet) (3 : Word) :=
  .backedge (next := bank 1 1 5) (by cbv)
    (.backedge (next := bank 2 1 4) (by cbv) (.exit (by cbv)))

example : computedTargets.1.runMain 14 0 (words meet) mem = .returned [3] mem := by cbv
example : (computedTargets.1.runMain 13 0 (words meet) mem).returnedValues? = none := by cbv
example : computedTargets.1.runMain 6 0 (words (bank 2 1 4)) mem = .returned [3] mem := by cbv
example : Generic.Fuel.run model (inputEnv model meet) 3 computedTargets.2 =
    some (0, Generic.packResult model (out := word) (3 : Word)) := by cbv

example : Eval (instruction model) (inputEnv model meet) computedTargets.2 mem 0
    (Generic.packResult model (out := word) (3 : Word)) mem :=
  (lambda_return_iff computedChecked computedAccepted _ _ _ _ _).mpr
    ⟨(3 : Word), (computedPlan.graph.returns_iff_mem_denote model _ _).mp ⟨2, computedReturns⟩, rfl, rfl, rfl⟩

example : ∀ returned final, ¬ computedTargets.1.oracle 0 (words spin) mem returned final :=
  (no_finite_return_iff computedChecked computedAccepted _ _).1.mpr
    (spinUndefined computedPlan (by cbv) (by cbv))

example : ∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin)
    computedTargets.2 mem label payload final :=
  (no_finite_return_iff computedChecked computedAccepted _ _).2.mpr
    (spinUndefined computedPlan (by cbv) (by cbv))

private def computedMapped := computedPlan.reindexInputs swap
private def computedReemitted : Checked.Phi.Targets :=
  (lowerBank computedMapped.graph, Generic.lower computedMapped.graph)

private theorem computedReindexed :
    lowerChecked 3 (computedSpec.reindexInputs swap) = some computedReemitted := by
  obtain ⟨p, found, emitted⟩ := lowerChecked_reindex swap computedAccepted
  cases Option.some.inj (found.symm.trans computedChecked)
  exact emitted

example : lowerChecked 3 (computedSpec.reindexInputs swap) = some computedReemitted := by cbv
example : bankHeader computedMapped.graph = bankHeader computedPlan.graph := rfl
example : computedReemitted.1.runMain 14 0 (words (bank 1 0 6)) mem = .returned [3] mem := by cbv
example : Generic.Fuel.run model (inputEnv model (bank 1 0 6)) 3 computedReemitted.2 =
    some (0, Generic.packResult model (out := word) (3 : Word)) := by cbv

example : Eval (instruction model) (inputEnv model (bank 1 0 6)) computedReemitted.2 mem 0
    (Generic.packResult model (out := word) (3 : Word)) mem := by
  apply (lambda_reindex_return_iff swap computedChecked computedReindexed _ _ _ _ _).mpr
  have sameInput : swap.pull (bank 1 0 6) = meet := by cbv
  rw [sameInput]
  exact ⟨3, (computedPlan.graph.returns_iff_mem_denote model _ _).mp ⟨2, computedReturns⟩, rfl, rfl, rfl⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
