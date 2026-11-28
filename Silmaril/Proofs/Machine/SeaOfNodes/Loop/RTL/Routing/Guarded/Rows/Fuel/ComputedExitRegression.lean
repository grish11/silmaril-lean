module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def spec : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 2]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .ne
  limit := 3
  exitSlot := 2
  exitOrigin := some (.output 1 0)

private def plan : Plan 3 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 2, 2, 1⟩]
  guardIndex := 0
  comparison := .ne
  limit := 3
  exitSlot := 2
  exitProducer := some 1

private def targets : Checked.Phi.Targets := (lowerBank plan.graph, Generic.lower plan.graph)
private theorem checked : checkPlan 3 spec = some plan := by cbv
private theorem accepted : lowerChecked 3 spec = some targets := by cbv

example : lowerChecked 3 { spec with exitOrigin := some (.output 0 0) } = none := by cbv
example : lowerChecked 3 { spec with exitOrigin := some (.output 1 1) } = none := by cbv

example : (bankHeader plan.graph).term.args[1]? = some (2, [Reg.node 1]) :=
  exit_operand plan

private def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))
private def input := bank 0 1 10
private def immediate := bank 2 1 10
private def spin := bank 1 0 10
private def mem := Memory.ofList 4 [29, 71, 53, 11]

private theorem nativeReturns :
    plan.graph.ReturnsAfter model input 2 (plan.graph.initial model input) (7 : Word) :=
  .backedge (next := bank 1 1 9) (by cbv)
    (.backedge (next := bank 2 1 8) (by cbv) (.exit (by cbv)))

-- Exchanging the exit producer for its old destination changes the observation.
example : ({ plan with exitProducer := none }).graph.evalBackedges model 2 input = some (8 : Word) := by cbv

example : targets.1.runMain 17 0 (words input) mem = .returned [7] mem :=
  (runMain_fuel_iff plan input mem mem [7] 17).mpr ⟨2, (7 : Word), nativeReturns, by decide, rfl, rfl⟩

example : targets.1.runMain 17 0 (words input) mem = .returned [7] mem := by cbv
example : targets.1.runMain 7 0 (words immediate) mem = .returned [9] mem := by cbv

example : Generic.Fuel.run model (inputEnv model input) 3 targets.2 =
    some (0, Generic.packResult model (out := word) (7 : Word)) := by cbv

example : Eval (instruction model) (inputEnv model input) targets.2 mem 0
    (Generic.packResult model (out := word) (7 : Word)) mem :=
  (lambda_return_iff checked accepted _ _ _ _ _).mpr
    ⟨(7 : Word), (plan.graph.returns_iff_mem_denote model _ _).mp ⟨2, nativeReturns⟩, rfl, rfl, rfl⟩

private theorem spinUndefined : plan.program.graph.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact plan.graph.not_returns_of_backedge_invariant model spin value (· = spin) (by cbv)
    (fun old fixed => by
      subst old
      exact ⟨spin, by cbv, rfl⟩)
    ((plan.graph.returns_iff_mem_denote model _ _).mpr present)

example : ∀ returned final, ¬ targets.1.oracle 0 (words spin) mem returned final :=
  (no_finite_return_iff checked accepted _ _).1.mpr spinUndefined

example : ∀ label payload final, ¬ Eval (instruction model) (inputEnv model spin)
    targets.2 mem label payload final :=
  (no_finite_return_iff checked accepted _ _).2.mpr spinUndefined

private def swap : InputPermutation 3 := Equiv.swap 0 1

private def reemitted : Checked.Phi.Targets :=
  (lowerBank (plan.reindexInputs swap).graph, Generic.lower (plan.reindexInputs swap).graph)

example : lowerChecked 3 (spec.reindexInputs swap) = some reemitted := by cbv
example : reemitted.1.runMain 17 0 (words (bank 1 0 10)) mem = .returned [7] mem := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
