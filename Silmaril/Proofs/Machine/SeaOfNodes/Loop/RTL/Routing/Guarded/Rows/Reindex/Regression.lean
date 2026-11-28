module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def spec : Spec :=
  ⟨[0, 1], [0, 1], [⟨.add, 0, 0, 1⟩], .output 0 0, 0, .ne, 3, 0, none, none⟩

private def plan : Plan 2 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
  updates := [⟨.add, 0, 0, 1⟩]
  guardIndex := 0
  comparison := .ne
  limit := 3
  exitSlot := 0

private def swap : InputPermutation 2 := Equiv.swap 0 1
private def mapped := plan.reindexInputs swap

private def original : Checked.Phi.Targets := (lowerBank plan.graph, Generic.lower plan.graph)
private def emitted : Checked.Phi.Targets := (lowerBank mapped.graph, Generic.lower mapped.graph)

private theorem checked : checkPlan 2 spec = some plan := by cbv
private theorem accepted : lowerChecked 2 spec = some original := by cbv

private theorem reemitted : lowerChecked 2 (spec.reindexInputs swap) = some emitted := by
  obtain ⟨p, found, result⟩ := lowerChecked_reindex swap accepted
  cases Option.some.inj (found.symm.trans checked)
  exact result

example : lowerChecked 2 (spec.reindexInputs swap) = some emitted := by cbv

example : lowerChecked 2 ({ spec with entry := [0, 2] }.reindexInputs swap) = none := by cbv

private def bank (x y : Word) : WordTuple 2 := .cons x (.cons y .nil)
private def initial := Memory.ofList 4 [29, 71, 53, 11]

example : swap.pull (bank 1 0) = bank 0 1 := by cbv
example : (bankPreheader mapped.graph).term = .jump 1 [.arg 1, .arg 0] := by cbv
example : bankHeader mapped.graph = bankHeader plan.graph := rfl

-- The swapped interface supplies the same old bank, (0, 1).
-- Each taken backedge increments slot 0 by old slot 1. Exit projects old slot 0.
private theorem nativeReturns :
    (2 : Word) ∈ plan.program.graph.denote model (swap.pull (bank 1 0)) := by
  apply (plan.graph.returns_iff_mem_denote model _ _).mp
  refine ⟨2, .backedge (next := bank 1 1) ?_ (.backedge (next := bank 2 1) ?_ (.exit ?_))⟩ <;> cbv

example : emitted.1.oracle 0 (words (bank 1 0)) initial [2] initial :=
  (rtl_reindex_return_iff swap checked reemitted _ _ _ _).mpr ⟨2, nativeReturns, rfl, rfl⟩

example : Eval (instruction model) (inputEnv model (bank 1 0)) emitted.2 initial 0
    (Generic.packResult model (out := word) (2 : Word)) initial :=
  (lambda_reindex_return_iff swap checked reemitted _ _ _ _ _).mpr ⟨2, nativeReturns, rfl, rfl, rfl⟩

example : emitted.1.runMain 14 0 (words (bank 1 0)) initial = .returned [2] initial := by cbv

example : Generic.Fuel.run model (inputEnv model (bank 1 0)) 3 emitted.2 =
    some (0, Generic.packResult model (out := word) (2 : Word)) := by cbv

-- The same raw tuple with the wrong interface starts at (1, 0) and spins.
private theorem nativeAbsent : plan.program.graph.denote model (bank 1 0) = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact plan.graph.not_returns_of_backedge_invariant model (bank 1 0) value
    (fun old => old = bank 1 0) (by cbv)
    (fun old fixed => by
      subst old
      exact ⟨bank 1 0, by cbv, rfl⟩)
    ((plan.graph.returns_iff_mem_denote model _ _).mpr present)

example : ∀ returned final, ¬ original.1.oracle 0 (words (bank 1 0)) initial returned final :=
  (no_finite_return_iff checked accepted _ _).1.mpr nativeAbsent

example : ∀ returned final, ¬ emitted.1.oracle 0 (words (bank 0 1)) initial returned final :=
  (reindex_no_finite_return_iff swap checked reemitted _ _).1.mpr nativeAbsent

example : ∀ label payload final, ¬ Eval (instruction model) (inputEnv model (bank 0 1))
    emitted.2 initial label payload final :=
  (reindex_no_finite_return_iff swap checked reemitted _ _).2.mpr nativeAbsent

private def arrivals : Fin 2 ≃ Incoming where
  toFun := Fin.cases .entry (fun _ => .backedge)
  invFun := Incoming.select 0 1
  left_inv := fun i => Fin.cases rfl (fun j => by rw [Fin.fin_one_eq_zero j]; rfl) i
  right_inv := fun arrival => by cases arrival <;> rfl

private def forward : Fin 2 ≃ Generic.HeaderIncoming mapped.graph :=
  arrivals.trans (Generic.headerIncomingEquiv mapped.graph)

private def reversed : Fin 2 ≃ Generic.HeaderIncoming mapped.graph :=
  (Equiv.swap 0 1).trans forward

example :
    Generic.slotBranch mapped.graph forward 0 = Generic.slotBranch mapped.graph reversed 1 ∧
    Generic.slotBranch mapped.graph forward 1 = Generic.slotBranch mapped.graph reversed 0 := by
  have f arrival := (incoming_alignment mapped forward arrival).2
  have r arrival := (incoming_alignment mapped reversed arrival).2
  exact ⟨(f .entry).trans (r .entry).symm, (f .backedge).trans (r .backedge).symm⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
