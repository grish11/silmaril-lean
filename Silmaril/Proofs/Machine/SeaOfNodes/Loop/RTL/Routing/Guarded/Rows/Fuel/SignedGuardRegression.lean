module

import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Reindex.Thms
import Mathlib.Logic.Equiv.Basic

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (WordOp model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Primitive inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

private def spec : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 2]
  updates := [⟨.add, 0, 0, 1⟩, ⟨.add, 2, 2, 1⟩]
  guardOrigin := .output 0 0
  guardDestination := 0
  comparison := .slt
  limit := 0
  guardRhs := some (.output 1 0)
  exitSlot := 2
  exitOrigin := some (.output 1 0)

private def plan : Plan 3 where
  entry := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  copies := .cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head))) .nil))
  updates := [⟨.add, 0, 0, 1⟩, ⟨.add, 2, 2, 1⟩]
  guardIndex := 0
  comparison := .slt
  limit := 0
  guardOperand := .computed 1
  exitSlot := 2
  exitProducer := some 1

private def targets : Checked.Phi.Targets := (lowerBank plan.graph, Generic.lower plan.graph)

private theorem checked : checkPlan 3 spec = some plan := by cbv
private theorem accepted : lowerChecked 3 spec = some targets := by cbv

example : lowerChecked 3 { spec with guardRhs := some (.output 1 1) } = none := by cbv
example : (lowerChecked 3 { spec with guardRhs := none }).isSome = true := by cbv
example : (lowerChecked 3 { spec with guardRhs := some (.arg 2) }).isSome = true := by cbv

example : (targets.1.block? 0 1).bind (fun block => block.ops[2]?) =
    some (.binary (.cmp .lts) (.node 2) (.node 0) (.node 1)) :=
  guard_compare_computed plan ⟨1, by decide⟩ rfl

example : (targets.1.block? 0 1).map (·.term) =
    some (.cond (.node 2) 1 [.node 0, .arg 4, .node 1] 2 [.node 1]) := by cbv

-- Read the comparison and both successor packets directly from the checked CFG.
private def headerWires (cfg : Region (Primitive WordOp)) : Prop :=
  match cfg with
  | .cfg _ n blocks =>
    if inside : 0 < n then
      match blocks ⟨0, inside⟩ with
      | .let₂ _ (.let₂ _ (.let₂ _ body)) =>
        match body with
        | .let₁ _ (.let₁ _ (.let₁ (.op (.apply .slt) (.pair (.var lhs) (.pair (.var rhs) .unit)))
            (.case (.var predicate) (.br 0 feedback) (.br 1 (.pair (.var result) .unit))))) =>
          (lhs, rhs, predicate, result) = (1, 0, 0, 2) ∧
            feedback = .pair (.var 3) (.pair (.var 7) (.pair (.var 2) .unit))
        | _ => False
      | _ => False
    else False
  | _ => False

example : headerWires targets.2 := by cbv

private def bank (x y z : Word) : WordTuple 3 := .cons x (.cons y (.cons z .nil))
private def signedMax : Word := 0x7fff_ffff_ffff_ffff
private def signedMin : Word := 0x8000_0000_0000_0000
private def crossing := bank (-2) 1 (signedMax - 1)
private def spin := bank (-1) 0 signedMax
private def mem := Memory.ofList 4 [29, 71, 53, 11]

-- The first comparison is -1 < maxSigned. Unsigned order and reversed
-- operands both exit immediately. On the next visit the RHS wraps to minSigned.
private theorem nativeReturns :
    plan.graph.ReturnsAfter model crossing 1 (plan.graph.initial model crossing) signedMin :=
  .backedge (next := bank (-1) 1 signedMax) (by cbv) (.exit (by cbv))

example : plan.graph.step model crossing (bank (-2) 1 (-2)) = .inl (-1 : Word) := by cbv

example : targets.1.runMain 10 0 (words crossing) mem = .returned [signedMin] mem :=
  (runMain_fuel_iff plan crossing mem mem [signedMin] 10).mpr
    ⟨1, signedMin, nativeReturns, by decide, rfl, rfl⟩

example : targets.1.runMain 10 0 (words crossing) mem = .returned [signedMin] mem := by cbv
example : (targets.1.runMain 9 0 (words crossing) mem).returnedValues? = none := by cbv
example : Generic.Fuel.run model (inputEnv model crossing) 2 targets.2 =
    some (0, Generic.packResult model (out := word) signedMin) := by cbv

private theorem nativeAbsent : plan.program.graph.denote model spin = Part.none := by
  rw [Part.eq_none_iff', Part.dom_iff_mem]
  rintro ⟨value, present⟩
  exact plan.graph.not_returns_of_backedge_invariant model spin value (· = spin) (by cbv)
    (fun old fixed => by
      subst old
      exact ⟨spin, by cbv, rfl⟩)
    ((plan.graph.returns_iff_mem_denote model _ _).mpr present)

private def swap : InputPermutation 3 := Equiv.swap 0 1
private def mapped := plan.reindexInputs swap
private def emitted : Checked.Phi.Targets := (lowerBank mapped.graph, Generic.lower mapped.graph)

private theorem reemitted : lowerChecked 3 (spec.reindexInputs swap) = some emitted := by
  obtain ⟨p, found, lowered⟩ := lowerChecked_reindex swap accepted
  cases Option.some.inj (found.symm.trans checked)
  exact lowered

private def swappedCrossing := bank 1 (-2) (signedMax - 1)

private theorem pulledReturn : signedMin ∈ plan.program.graph.denote model (swap.pull swappedCrossing) := by
  have pull : swap.pull swappedCrossing = crossing := by cbv
  rw [pull]
  exact (plan.graph.returns_iff_mem_denote model _ _).mp ⟨1, nativeReturns⟩

example : emitted.1.oracle 0 (words swappedCrossing) mem [signedMin] mem :=
  (rtl_reindex_return_iff swap checked reemitted _ _ _ _).mpr ⟨signedMin, pulledReturn, rfl, rfl⟩

example : Eval (instruction model) (inputEnv model swappedCrossing) emitted.2
    mem 0 (Generic.packResult model (out := word) signedMin) mem :=
  (lambda_reindex_return_iff swap checked reemitted _ _ _ _ _).mpr
    ⟨signedMin, pulledReturn, rfl, rfl, rfl⟩

example : rtlObservation emitted.1 swappedCrossing mem = lambdaObservation emitted.2 swappedCrossing mem :=
  (reindex_equation_at_iff swap checked checked reemitted reemitted _ _).mpr rfl

example :
    (∀ returned final, ¬ emitted.1.oracle 0 (words (bank 0 (-1) signedMax)) mem returned final) ∧
    (∀ label payload final, ¬ Eval (instruction model) (inputEnv model (bank 0 (-1) signedMax))
      emitted.2 mem label payload final) := by
  have pull : swap.pull (bank 0 (-1) signedMax) = spin := by cbv
  have absent := reindex_no_finite_return_iff swap checked reemitted (bank 0 (-1) signedMax) mem
  rw [pull] at absent
  exact ⟨absent.1.mpr nativeAbsent, absent.2.mpr nativeAbsent⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
