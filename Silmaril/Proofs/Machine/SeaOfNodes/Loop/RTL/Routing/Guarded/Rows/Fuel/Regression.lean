module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def spec : Spec :=
  ⟨[0, 1, 2], [0, 1, 0], [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩], .output 1 0, 0, .ne, 14, 2⟩

private def plan : Plan 3 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil))
  updates := [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩]
  guardIndex := 1
  comparison := .ne
  limit := 14
  exitSlot := 2

private def targets : Checked.Phi.Targets := (lowerBank plan.graph, Generic.lower plan.graph)
private theorem accepted : lowerChecked 3 spec = some targets := by cbv

private def tuple (a b c : Word) : WordTuple 3 := .cons a (.cons b (.cons c .nil))
private def input := tuple 5 2 20
private def immediate := tuple 12 2 20
private def mem : Memory := Memory.ofList 4 [29, 71, 53, 11]

example : checkPlan 3 spec = some plan := by cbv
example : plan.rtlFuel 0 = 7 := rfl
example : plan.rtlFuel 2 = 17 := rfl

private theorem sourceTwo :
    plan.graph.ReturnsAfter model input 2 (plan.graph.initial model input) (7 : Word) :=
  .backedge (next := tuple 7 3 5) (by cbv)
    (.backedge (next := tuple 10 4 7) (by cbv) (.exit (by cbv)))

private theorem machineTwo : targets.1.runMain 17 0 (words input) mem = .returned [7] mem :=
  (runMain_fuel_iff plan input mem mem [7] 17).mpr ⟨2, (7 : Word), sourceTwo, by decide, rfl, rfl⟩

example : targets.1.runMain 17 0 (words input) mem = .returned [7] mem := by cbv
example : (targets.1.runMain 16 0 (words input) mem).returnedValues? = none := by cbv

example :
    match targets.1.runMain 16 0 (words input) mem with
    | .running state => state.mem = mem
    | _ => False := by cbv

example : targets.1.runMain 7 0 (words immediate) mem = .returned [20] mem := by cbv
example : Generic.Fuel.run model (inputEnv model immediate) 1 targets.2 =
    some (0, Generic.packResult model (out := word) (20 : Word)) := by cbv

example : Generic.Fuel.run model (inputEnv model input) 2 targets.2 = none := by cbv
example : (targets.1.runMain (plan.rtlFuel 1) 0 (words input) mem).returnedValues? = none :=
  (bounded_absence_iff plan input mem 1).mpr (by cbv)

private theorem lambdaTwo : Generic.Fuel.run model (inputEnv model input) 3 targets.2 =
    some (0, Generic.packResult model (out := word) (7 : Word)) := by cbv

example : targets.1.runMain (plan.rtlFuel 2) 0 (words input) mem = .returned [7] mem :=
  (bounded_returns_iff plan input mem mem [7] 2).mpr ⟨7, lambdaTwo, rfl, rfl⟩

example : Eval (instruction model) (inputEnv model input) targets.2
    mem 0 (Generic.packResult model (out := word) (7 : Word)) mem := by
  have native : targets.1.oracle 0 (words input) mem [7] mem :=
    (rtl_returns_iff plan input mem mem [7]).mpr ⟨7, ⟨2, sourceTwo⟩, rfl, rfl⟩
  obtain ⟨value, same, eval⟩ := (returns_iff accepted input mem mem [7]).mp native
  cases same
  exact eval

private def entryFirst : Fin 2 ≃ Incoming where
  toFun := Fin.cases .entry (fun _ => .backedge)
  invFun := Incoming.select 0 1
  left_inv := fun i => Fin.cases rfl (fun j => by rw [Fin.fin_one_eq_zero j]; rfl) i
  right_inv := fun arrival => by cases arrival <;> rfl

private def forward : Fin 2 ≃ Generic.HeaderIncoming plan.graph :=
  entryFirst.trans (Generic.headerIncomingEquiv plan.graph)

private def reversed : Fin 2 ≃ Generic.HeaderIncoming plan.graph :=
  (Equiv.swap 0 1).trans forward

-- Positional readback preserves the actual branches of the CFG in this run.
example :
    Generic.slotBranch plan.graph forward 1 = Generic.slotBranch plan.graph reversed 0 ∧
    Generic.slotBranch plan.graph forward 0 = Generic.slotBranch plan.graph reversed 1 ∧
    targets.1.runMain 17 0 (words input) mem = .returned [7] mem := by
  have f arrival := (incoming_alignment plan forward arrival).2
  have r arrival := (incoming_alignment plan reversed arrival).2
  exact ⟨(f .backedge).trans (r .backedge).symm, (f .entry).trans (r .entry).symm, machineTwo⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
