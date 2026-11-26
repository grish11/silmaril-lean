module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Thms
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine
open Diamond (Ty Val ValueSort dataPorts)
open GVN (newest read_newest read_weaken weaken)
open GVN.Elimination (Rewrite Routing read_splitOrigin splitOrigin)
open SubZero (model wordPort)
open Silmaril.SSA.RVSDG (Locals Tuple Wires)

variable {args : List (Ty Unit)} {past : List (List (Ty Unit))}
variable {ins inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}
variable {known : Prefix args past}

theorem match_exact {lhs rhs : WordWire args past} {edit : AddRewrite.Splice args past}
    (accepted : matchAdd? known lhs rhs = some edit) :
    (known.literals lhs).isNone = true ∧ (known.literals rhs).isNone = true ∧ lhs.address ≠ rhs.address ∧
      ∃ left right, known.addends lhs = some left ∧ known.addends rhs = some right ∧
        edit = rotate lhs right := by
  unfold matchAdd? at accepted
  split at accepted
  · rename_i guard
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    obtain ⟨left, leftFound, accepted⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨right, rightFound, rfl⟩ := Option.map_eq_some_iff.mp accepted
    exact ⟨guard.1.1, guard.1.2, guard.2, left, right, leftFound, rightFound, rfl⟩
  · cases accepted

private abbrev readWord (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past)
    (wire : WordWire args past) : BitVec 64 :=
  Diamond.read model wire entry locals

private theorem extend_agrees (agree : Addends.Agree known.addends entry locals)
    {value : BitVec 64} {fresh : Option (Addends args past)}
    (freshSound : ∀ pair, fresh = some pair → value = pair.eval entry locals) :
    Addends.Agree (known.extendAddends fresh) entry (locals.snoc (.cons value .nil)) := by
  intro wire pair found
  let next : Tuple (Val model.value) [wordPort] := .cons value .nil
  have read := read_splitOrigin wire model entry locals next
  have weakening (original : Addends args past) :
      original.weaken.eval entry (locals.snoc next) = original.eval entry locals := by
    simp only [Addends.eval, Addends.weaken, read_weaken]
  cases source : splitOrigin [wordPort] wire with
  | inl prior =>
    simp only [Prefix.extendAddends, source] at found
    obtain ⟨original, fromPrior, rfl⟩ := Option.map_eq_some_iff.mp found
    simp only [source] at read
    exact read.symm.trans ((agree prior original fromPrior).trans (weakening original).symm)
  | inr port =>
    cases port with
    | head =>
      simp only [Prefix.extendAddends, source] at found
      obtain ⟨original, fromNew, rfl⟩ := Option.map_eq_some_iff.mp found
      simp only [source] at read
      exact read.symm.trans ((freshSound original fromNew).trans (weakening original).symm)
    | tail empty => nomatch empty

private theorem record_addends_agree (agree : Addends.Agree known.addends entry locals)
    (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins)) :
    Addends.Agree (known.record op operands).addends entry
      (locals.snoc (.cons (model.run op (operands.read entry locals)) .nil)) := by
  cases op with
  | literal | sub | mul => exact extend_agrees agree (fun _ impossible => by cases impossible)
  | add =>
    cases operands with
    | cons lhs tail =>
      cases tail with
      | cons rhs empty =>
        cases empty
        exact extend_agrees agree (fun _ found => by cases Option.some.inj found; rfl)

private theorem rotate_eval (left : WordWire args past) (right : Addends args past) :
    (rotate left right).eval entry locals =
      (readWord entry locals left + readWord entry locals right.left) + readWord entry locals right.right := by
  let value := readWord entry locals left + readWord entry locals right.left
  let fresh : Tuple (Val model.value) [wordPort] := .cons value .nil
  change readWord entry (locals.snoc fresh) (newest .head) +
    readWord entry (locals.snoc fresh) (weaken [wordPort] right.right) = _
  simp only [readWord, read_newest, read_weaken]
  rfl

theorem record_agrees (agree : known.Agrees entry locals)
    (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins)) :
    (known.record op operands).Agrees entry
      (locals.snoc (.cons (model.run op (operands.read entry locals)) .nil)) :=
  ⟨Scan.Rule.record_agrees agree.1 (arithmeticRules op) operands, record_addends_agree agree.2 op operands⟩

theorem empty_agrees (entry : Tuple (Val model.value) args) :
    (Prefix.empty (args := args)).Agrees entry PUnit.unit := by
  constructor
  · intro t wire value impossible
    cases impossible
  · intro wire pair impossible
    cases impossible

private def sound (entry : Tuple (Val model.value) args) : AddRewrite.Sound rules entry where
  Agrees known locals := known.Agrees entry locals
  record op operands agree := record_agrees agree op operands
  replaceAdd := by
    intro past facts locals lhs rhs edit agree accepted
    obtain ⟨_, _, _, _, right, _, rightFound, rfl⟩ := match_exact accepted
    have readRight : readWord entry locals rhs = right.eval entry locals := agree.2 rhs right rightFound
    change readWord entry _ lhs + readWord entry _ rhs = _
    rw [readRight, rotate_eval]
    exact (BitVec.add_assoc _ _ _).symm

variable {program : Program SubZero.Opcode inputs out}
variable {rewrite : Rewrite SubZero.Opcode (dataPorts inputs) [] program.sigs}

theorem step_agrees (accepted : step? program = some rewrite)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    Routing.Agrees rewrite.route model entry (program.dataflow.eval model entry PUnit.unit)
      (rewrite.flow.eval model entry PUnit.unit) :=
  AddRewrite.scan_agrees (sound entry) program.dataflow (empty_agrees entry) accepted

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine
