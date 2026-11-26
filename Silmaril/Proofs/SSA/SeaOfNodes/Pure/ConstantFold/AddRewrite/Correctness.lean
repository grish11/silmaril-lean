module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite
open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (newest read_newest read_weaken weaken)
open GVN.Elimination (Rewrite Routing routeSuffix routeSuffix_agrees)
open SubZero (model wordPort)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}
variable {Facts : List (List (Ty Unit)) → Type} {rules : Rules args Facts} {facts : Facts past}
variable {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}

theorem splice_eval (edit : Edit args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) :
    edit.splice.eval entry locals = edit.eval entry locals := by
  let literal : Tuple (Val model.value) [wordPort] := .cons edit.right .nil
  change model.run edit.opcode
    (.cons (Diamond.read model (weaken [wordPort] edit.left) entry (locals.snoc literal))
      (.cons (Diamond.read model (newest .head) entry (locals.snoc literal)) .nil)) = edit.eval entry locals
  simp only [read_weaken, read_newest]
  rfl

private theorem insert_agrees (lhs rhs : Origin args past wordPort) (edit : Splice args past)
    (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs)
    (equal :
      model.run .add (.cons (Diamond.read model lhs entry locals) (.cons (Diamond.read model rhs entry locals) .nil)) =
        edit.eval entry locals) :
    let original := Dataflow.cons SubZero.Opcode.add (.cons lhs (.cons rhs .nil)) rest
    let rewritten := insertSplice edit rest
    Routing.Agrees rewritten.route model entry (original.eval model entry locals)
      (rewritten.flow.eval model entry locals) := by
  let fresh : Tuple (Val model.value) [wordPort] := .cons (edit.privateBinding.eval entry locals) .nil
  let lifted : Routing args past (past ++ [[wordPort]]) := fun wire => weaken [wordPort] wire
  have liftedAgrees : Routing.Agrees lifted model entry locals (locals.snoc fresh) :=
    fun _ wire => (read_weaken wire model entry locals fresh).symm
  let originalValue := model.run .add
    (.cons (Diamond.read model lhs entry locals) (.cons (Diamond.read model rhs entry locals) .nil))
  let suffix := routeSuffix rest (lifted.push [wordPort])
  change Routing.Agrees suffix.2 model entry
    (rest.eval model entry (locals.snoc (.cons originalValue .nil)))
    (suffix.1.eval model entry ((locals.snoc fresh).snoc (.cons (edit.eval entry locals) .nil)))
  rw [← equal]
  exact routeSuffix_agrees rest _ model entry _ _ (Routing.push_agrees liftedAgrees _)

private theorem head_agrees (sound : Sound rules entry) (agree : sound.Agrees facts locals)
    (op : SubZero.Opcode ins out) (operands : Wires args past (dataPorts ins))
    (rest : Dataflow SubZero.Opcode args (past ++ [[.value out]]) sigs)
    {rewrite : Rewrite SubZero.Opcode args past ([.value out] :: sigs)}
    (accepted : atHead? rules facts op operands rest = some rewrite) :
    Routing.Agrees rewrite.route model entry ((Dataflow.cons op operands rest).eval model entry locals)
      (rewrite.flow.eval model entry locals) := by
  cases op with
  | literal | sub | mul => cases accepted
  | add =>
    cases operands with
    | cons lhs tail =>
      cases tail with
      | cons rhs empty =>
        cases empty
        obtain ⟨edit, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
        exact insert_agrees lhs rhs edit rest (sound.replaceAdd agree found)

theorem scan_agrees (sound : Sound rules entry) (flow : Dataflow SubZero.Opcode args past sigs)
    (agree : sound.Agrees facts locals) {rewrite : Rewrite SubZero.Opcode args past sigs}
    (accepted : scan? rules facts flow = some rewrite) :
    Routing.Agrees rewrite.route model entry (flow.eval model entry locals) (rewrite.flow.eval model entry locals) := by
  induction flow with
  | nil => cases accepted
  | cons op operands rest ih =>
    simp only [scan?] at accepted
    split at accepted
    · rename_i found head
      cases Option.some.inj accepted
      exact head_agrees sound agree op operands rest head
    · obtain ⟨suffix, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact ih (sound.record op operands agree) found

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite
