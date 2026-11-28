module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup

open Pure.SubZero (model word)
open GVN.Elimination (Rewrite Routing)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Suffix} {edit : Rewrite Pure.SubZero.Opcode (dataPorts [word, word]) [] p.sigs}
variable {intermediate : Result inputs sigs} {target : Program inputs sigs [word]}

/-- Every old typed suffix read agrees through the edit's use redirection. -/
theorem suffixEdit?_agrees (accepted : suffixEdit? p = some edit)
    (entry : Tuple (Val model.value) (dataPorts [word, word])) :
    Routing.Agrees edit.route model entry (p.dataflow.eval model entry PUnit.unit)
      (edit.flow.eval model entry PUnit.unit) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.suffixEdit?_agrees accepted entry

/-- The deleted inner result routes to the capture. The old outer result
is now producer 1 and reads the capture and the live join word in that order. -/
theorem suffixEdit?_redirects
    {edit : Rewrite Pure.SubZero.Opcode (dataPorts [word, word]) [] (suffix .left 0).sigs}
    (accepted : suffixEdit? (suffix .left 0) = some edit) :
    edit.route (.output (1 : Fin 3) .head) = .arg .head ∧
      (edit.route (.output (2 : Fin 3) .head)).address = .output 1 0 ∧
      Pure.ConstantFold.AddRewrite.rewrittenProgram (suffix .left 0) edit = cleanedSuffix :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.suffixEdit?_redirects accepted

/-- Admission checks the actual suffix. On success the exact diamond,
including each surviving occurrence wire and its producer scope, is retained. -/
theorem rewrite?_eq_some_iff :
    rewrite? intermediate = some target ↔
      ∃ value p, intermediate = .materialized .left value p ∧
        p.suffix = suffix .left 0 ∧ target = { p with suffix := cleanedSuffix } :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.rewrite?_eq_some_iff

/-- The cleanup preserves the returned value at each predecessor occurrence. -/
theorem rewrite?_atSlot_eq {value : BitVec 64} {before : Program inputs sigs [word]}
    (accepted : rewrite? (.materialized .left value before) = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = before.atSlot entry slot :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.rewrite?_atSlot_eq accepted entry slot

/-- The cleaned program preserves and reflects finite returns of the intermediate. -/
theorem rewrite?_returns_iff (accepted : rewrite? intermediate = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ intermediate.Returns entry returned :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.rewrite?_returns_iff accepted entry returned

/-- Running the two checked steps preserves and reflects finite returns
of the original two-Φ program for every typed input. -/
theorem materialize_then_rewrite?_returns_iff {g : AddPhi.Pair.Source inputs sigs}
    {x : InputWord inputs} {first : Column}
    (materialized : Materialize.rewrite g x first = .ok intermediate)
    (accepted : rewrite? intermediate = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ (original g x).Returns entry returned :=
  (rewrite?_returns_iff accepted entry returned).trans (rewrite_returns_iff materialized entry returned)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup
