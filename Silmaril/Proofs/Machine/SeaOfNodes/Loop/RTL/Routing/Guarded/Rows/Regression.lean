module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Steps)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (encodeTuple inputEnv instruction)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def spec : Spec :=
  ⟨[0, 1, 2], [0, 1, 0], [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩], .output 1 0, 0, .eq, 7, 2⟩

private def plan : Plan 3 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil))
  updates := [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩]
  guardIndex := 1
  comparison := .eq
  limit := 7
  exitSlot := 2

private def targets : Checked.Phi.Targets := (lowerBank plan.graph, Generic.lower plan.graph)
private theorem accepted : lowerChecked 3 spec = some targets := by cbv
example : checkPlan 3 spec = some plan := by cbv
example : targets.1.WellFormed := (lowerChecked_typed accepted).1

private def triple (a b c : Word) : WordTuple 3 := .cons a (.cons b (.cons c .nil))
private def input : WordTuple 3 := triple 5 2 20
private def feedback : WordTuple 3 := triple 7 3 5
private def mem : Memory := Memory.ofList 4 [29, 71, 53, 11]
private def frame (a : Word) : Frame Reg := bindWords 3 (bindWords 0 Frame.empty input) (triple a 2 20)

private theorem oldMatches (a : Word) : ArgsMatch (frame a) (appendTuple (triple a 2 20) input) := by
  intro port
  repeat' first | rfl | casesm Silmaril.SSA.RVSDG.Port _ _

example : plan.guardValue input = 7 := by cbv
example : plan.nextBank input input = feedback := by cbv
example : bankIncoming plan.graph .backedge = [.node 1, .node 0, .arg 3] := by cbv

-- The first producer overwrites slot 1. The second uses old slot 1, and
-- the third field copies old slot 0.
example :
    Steps targets.1 ⟨⟨0, 1, 0⟩, frame 5, [], mem⟩
      ⟨⟨0, 1, 0⟩, bindWords 3 (plan.testFrame (frame 5) input) feedback, [], mem⟩ ∧
    Eval (instruction model) (extend (inputEnv model input) (encodeTuple model input))
      (Generic.header plan.graph) mem 0 (encodeTuple model feedback) mem := by
  have run := activation_agrees plan input input (frame 5) mem (oldMatches 5)
  exact run

example :
    Steps targets.1 ⟨⟨0, 1, 0⟩, frame 6, [], mem⟩
      ⟨⟨0, 2, 0⟩, (plan.testFrame (frame 6) (triple 6 2 20)).set .phi 20, [], mem⟩ ∧
    Eval (instruction model) (extend (inputEnv model input) (encodeTuple model (triple 6 2 20)))
      (Generic.header plan.graph) mem 1 (Generic.packResult model (out := word) (20 : Word)) mem :=
  activation_agrees plan input (triple 6 2 20) (frame 6) mem (oldMatches 6)

private def entryFirst : Fin 2 ≃ Incoming where
  toFun := Fin.cases .entry (fun _ => .backedge)
  invFun := Incoming.select 0 1
  left_inv := fun i => Fin.cases rfl (fun j => by rw [Fin.fin_one_eq_zero j]; rfl) i
  right_inv := fun arrival => by cases arrival <;> rfl

private def forward : Fin 2 ≃ Generic.HeaderIncoming plan.graph :=
  entryFirst.trans (Generic.headerIncomingEquiv plan.graph)

private def reversed : Fin 2 ≃ Generic.HeaderIncoming plan.graph :=
  (Equiv.swap 0 1).trans forward

example : Generic.slotBranch plan.graph forward 1 = Generic.slotBranch plan.graph reversed 0 := rfl
example : Generic.slotBranch plan.graph forward 0 = Generic.slotBranch plan.graph reversed 1 := rfl

example : targets.1.runMain 12 0 (words input) mem = .returned [5] mem := by cbv
example : Generic.Fuel.run model (inputEnv model input) 2 targets.2 =
    some (0, Generic.packResult model (out := word) (5 : Word)) := by cbv

-- Producer 0 is a valid word origin, but it writes slot 1, not the guard's slot 0.
example : lowerChecked 3 { spec with guardOrigin := .output 0 0 } = none := by cbv

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
