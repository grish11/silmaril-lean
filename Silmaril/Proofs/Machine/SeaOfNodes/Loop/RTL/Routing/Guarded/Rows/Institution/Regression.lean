module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def exitSpec : Spec :=
  ⟨[0, 1], [0, 1], [⟨.add, 0, 0, 1⟩], .output 0 0, 0, .ne, 3, 0⟩

private def spinSpec : Spec :=
  { exitSpec with entry := [0, 0], updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 1, 1, 1⟩] }

private def exitPlan : Plan 2 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
  updates := [⟨.add, 0, 0, 1⟩]
  guardIndex := 0
  comparison := .ne
  limit := 3
  exitSlot := 0

private def spinPlan : Plan 2 :=
  { exitPlan with
    entry := .cons (.arg .head) (.cons (.arg .head) .nil)
    updates := [⟨.add, 0, 0, 1⟩, ⟨.sub, 1, 1, 1⟩]
    guardIndex := 0 }

private def exitTargets : Checked.Phi.Targets :=
  (lowerBank exitPlan.graph, Generic.lower exitPlan.graph)

private def spinTargets : Checked.Phi.Targets :=
  (lowerBank spinPlan.graph, Generic.lower spinPlan.graph)

private theorem exitChecked : checkPlan 2 exitSpec = some exitPlan := by cbv
private theorem spinChecked : checkPlan 2 spinSpec = some spinPlan := by cbv
private theorem exitLowered : lowerChecked 2 exitSpec = some exitTargets := by cbv
private theorem spinLowered : lowerChecked 2 spinSpec = some spinTargets := by cbv

private def bank (x y : Word) : WordTuple 2 := .cons x (.cons y .nil)
private def input := bank 0 1
private def initial := Memory.ofList 4 [29, 71, 53, 11]

-- Step three guards on 3 and returns the old slot 0, which is 2.
private theorem exits :
    exitPlan.graph.ReturnsAfter model input 2 (exitPlan.graph.initial model input) (2 : Word) :=
  .backedge (next := bank 1 1) (by cbv)
    (.backedge (next := bank 2 1) (by cbv) (.exit (by cbv)))

private theorem spinUndefined : spinPlan.program.graph.denote model input = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨result, observed⟩
  have returns := (spinPlan.graph.returns_iff_mem_denote model input result).mpr observed
  exact spinPlan.graph.not_returns_of_backedge_invariant model input result
    (fun old => old = bank 0 0) (by cbv)
    (fun old fixed => by
      subst old
      exact ⟨bank 0 0, by cbv, rfl⟩) returns

-- One allowed backedge yields no observation from either target for either
-- plan. The two rows use different RTL budgets.
example : exitPlan.rtlFuel 1 = 10 ∧ spinPlan.rtlFuel 1 = 12 := ⟨rfl, rfl⟩

example :
    ((exitTargets.1.runMain 10 0 (words input) initial).returnedValues?,
      Generic.Fuel.run model (inputEnv model input) 2 exitTargets.2) = (none, none) := by cbv

example :
    ((spinTargets.1.runMain 12 0 (words input) initial).returnedValues?,
      Generic.Fuel.run model (inputEnv model input) 2 spinTargets.2) = (none, none) := by cbv

example : exitTargets.1.runMain 14 0 (words input) initial = .returned [2] initial := by cbv

example : Generic.Fuel.run model (inputEnv model input) 3 exitTargets.2 =
    some (0, Generic.packResult model (out := word) (2 : Word)) := by cbv

private theorem distinguishes :
    rtlObservation exitTargets.1 input initial ≠ lambdaObservation spinTargets.2 input initial := by
  intro same
  have native := (equation_at_iff exitChecked spinChecked exitLowered spinLowered input initial).mp same
  have present := (exitPlan.graph.returns_iff_mem_denote model input (2 : Word)).mp ⟨2, exits⟩
  change (2 : Word) ∈ exitPlan.program.graph.denote model input at present
  rw [native, spinUndefined] at present
  exact Part.notMem_none _ present

example : ¬ (exitPlan.equation spinPlan).Holds model := fun holds =>
  distinguishes ((equation_holds_iff exitChecked spinChecked exitLowered spinLowered initial).mp holds input)

example : (exitPlan.equation exitPlan).Holds model := fun _ => rfl

example : rtlObservation exitTargets.1 input initial = lambdaObservation exitTargets.2 input initial :=
  (equation_at_iff exitChecked exitChecked exitLowered exitLowered input initial).mpr rfl

example : ∀ returned final, ¬ spinTargets.1.oracle 0 (words input) initial returned final :=
  (no_finite_return_iff spinChecked spinLowered input initial).1.mpr spinUndefined

example : ∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
    spinTargets.2 initial label payload final :=
  (no_finite_return_iff spinChecked spinLowered input initial).2.mpr spinUndefined

private def arrivals : Fin 2 ≃ Incoming where
  toFun := Fin.cases .entry (fun _ => .backedge)
  invFun := Incoming.select 0 1
  left_inv := fun i => Fin.cases rfl (fun j => by rw [Fin.fin_one_eq_zero j]; rfl) i
  right_inv := fun arrival => by cases arrival <;> rfl

private def forward : Fin 2 ≃ Generic.HeaderIncoming exitPlan.program.graph :=
  arrivals.trans (Generic.headerIncomingEquiv exitPlan.program.graph)

private def reversed : Fin 2 ≃ Generic.HeaderIncoming exitPlan.program.graph :=
  (Equiv.swap 0 1).trans forward

example :
    Generic.slotBranch exitPlan.program.graph forward 0 = Generic.slotBranch exitPlan.program.graph reversed 1 ∧
    Generic.slotBranch exitPlan.program.graph forward 1 = Generic.slotBranch exitPlan.program.graph reversed 0 := by
  have f arrival := (incoming_alignment exitPlan forward arrival).2
  have r arrival := (incoming_alignment exitPlan reversed arrival).2
  exact ⟨(f .entry).trans (r .entry).symm, (f .backedge).trans (r .backedge).symm⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
