module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling
open Diamond (Ty Val ValueSort dataPorts)
open GVN.Elimination (Rewrite Routing)
open SubZero (model wordPort)
open Silmaril.SSA.RVSDG (Origin Tuple Wires)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {known : Literals args past} {lhs rhs : Origin args past wordPort} {edit : AddRewrite.Edit args past}

theorem match_exact (accepted : matchAdd? known lhs rhs = some edit) :
    lhs = rhs ∧ edit = ⟨.mul, lhs, 2⟩ := by
  unfold matchAdd? at accepted
  split at accepted
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    have wires := Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective
      (.cons lhs .nil) (.cons rhs .nil) (congrArg (fun address => [address]) guard.2)
    exact ⟨congrArg (fun pair : Wires args past [wordPort] => pair.get .head) wires,
      (Option.some.inj accepted).symm⟩
  · cases accepted

private theorem mul_two (value : BitVec 64) : value + value = value * 2 := by
  have mul_one : value * (1 : BitVec 64) = value := BitVec.mul_one value
  calc
    value + value = value * (1 + 1) := by rw [BitVec.mul_add, mul_one]
    _ = value * 2 := rfl

private def sound (entry : Tuple (Val model.value) args) : AddRewrite.Sound rules entry where
  Agrees known locals := Scan.Literals.Agrees known entry locals
  record op operands agree := Scan.Rule.record_agrees agree (arithmeticRules op) operands
  replaceAdd agree accepted := by
    obtain ⟨edit, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
    obtain ⟨rfl, rfl⟩ := match_exact found
    rw [AddRewrite.Edit.splice_eval]
    exact mul_two _

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit} {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  AddRewrite.scan_agrees (sound entry) program.dataflow (by intro t wire value impossible; cases impossible) accepted

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling
