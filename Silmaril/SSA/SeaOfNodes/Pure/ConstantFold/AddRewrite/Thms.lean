module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite

open Diamond (Dataflow Ty Val)
open GVN.Elimination (Rewrite Routing)
open SubZero (model wordPort)
open RVSDG (Locals Origin Tuple)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {Facts : List (List (Ty Unit)) → Type} {rules : Rules args Facts} {facts : Facts past}
variable {entry : Tuple (Val model.value) args} {locals : Locals (Val model.value) past}

/-- The generalized insertion interprets a right-literal edit as before. -/
theorem Edit.splice_eval (edit : Edit args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) :
    edit.splice.eval entry locals = edit.eval entry locals :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.splice_eval edit entry locals

/-- A checked insertion preserves all original reads through the suffix. -/
theorem insertSplice_agrees (lhs rhs : Origin args past wordPort) (edit : Splice args past)
    (rest : Dataflow SubZero.Opcode args (past ++ [[wordPort]]) sigs)
    (equal : evalAdd lhs rhs entry locals = edit.eval entry locals) :
    let original := Dataflow.cons SubZero.Opcode.add (.cons lhs (.cons rhs .nil)) rest
    let rewrite := insertSplice edit rest
    Routing.Agrees rewrite.route model entry (original.eval model entry locals)
      (rewrite.flow.eval model entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.insert_agrees lhs rhs edit rest equal

/-- A checked add rewrite preserves every original read through its typed map. -/
theorem scan_agrees (sound : Sound rules entry) (flow : Dataflow SubZero.Opcode args past sigs)
    (agree : sound.Agrees facts locals) {rewrite : Rewrite SubZero.Opcode args past sigs}
    (accepted : scan? rules facts flow = some rewrite) :
    Routing.Agrees rewrite.route model entry (flow.eval model entry locals) (rewrite.flow.eval model entry locals) :=
  Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite.scan_agrees sound flow agree accepted

end Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddRewrite
