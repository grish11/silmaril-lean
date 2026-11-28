module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize

open Pure.SubZero (model)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs} {first column : Column}
variable {value : BitVec 64} {result : Result inputs sigs}

/-- A checked constant is the selected column's value on either predecessor. -/
theorem constantColumns_slot_eq (found : constantColumns g column = some value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    ((g.arms slot).eval model entry (g.shared.eval model entry PUnit.unit)).get column.port = value :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.constantColumns_slot_eq found entry slot

/-- An admitted first binding takes precedence over the other binding. -/
theorem select_eq_some_iff :
    select g first = some (column, value) ↔
      (column = first ∧ constantColumns g column = some value) ∨
      (column = first.other ∧ constantColumns g first = none ∧ constantColumns g column = some value) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.select_eq_some_iff

/-- Replacing one column preserves the return at each original predecessor. -/
theorem emit_slot_eval_eq (found : constantColumns g column = some value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (emit g x column value).atSlot entry slot = (original g x).atSlot entry slot :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.emit_slot_eval_eq found entry slot

/-- The adapter emits the exact selected materialization or the existing
dispatcher result when neither column has a certificate. -/
theorem rewrite_eq_ok_iff :
    rewrite g x first = .ok result ↔
      (∃ column value, select g first = some (column, value) ∧
        result = .materialized column value (emit g x column value)) ∨
      (select g first = none ∧
        ∃ rotated, Dispatch.rewrite g x = .ok rotated ∧ result = .rotated rotated) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.rewrite_eq_ok_iff

/-- Both the intermediate materialization and delegated rewrites preserve
and reflect finite returns for every typed input. -/
theorem rewrite_returns_iff (accepted : rewrite g x first = .ok result)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    result.Returns entry returned ↔ (original g x).Returns entry returned :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.rewrite_returns_iff accepted entry returned

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize
