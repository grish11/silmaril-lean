module

public import Silmaril.Languages.Python.Core.Closure.Executor.Thms

/-! # Ordered scalar tuple returns -/

public section
namespace Silmaril.Languages.Python.Core.Closure.Executor

variable {layout : Layout} {globals : GlobalLookup} {heap : Heap} {frame : Frame layout}
  {items : List (TupleItem layout)}

theorem tuple_read_error {error : Failure}
    (read : items.mapM (TupleItem.evalIn globals heap frame) = .error error) :
    evalTupleIn globals heap frame items = .error error := by
  simp [evalTupleIn, evalTupleContentsIn, assembleFlatTuple, Except.map, read, Except.bind]

theorem tuple_ordered {values : List Value} {scalars : List Core.Module.TupleDispatch.Element}
    (reads : items.mapM (TupleItem.evalIn globals heap frame) = .ok values)
    (checked : values.mapM Value.tupleElement? = some scalars) :
    evalTupleIn globals heap frame items = .ok (.tuple scalars) := by
  simp [evalTupleIn, evalTupleContentsIn, assembleFlatTuple, Except.map, reads, checked, Except.bind]

theorem tuple_unsupportedElement {values : List Value}
    (reads : items.mapM (TupleItem.evalIn globals heap frame) = .ok values)
    (outside : values.mapM Value.tupleElement? = none) :
    evalTupleIn globals heap frame items = .error .unsupportedTupleElement := by
  simp [evalTupleIn, evalTupleContentsIn, assembleFlatTuple, Except.map, reads, outside, Except.bind]

theorem tuple_return {scalars : List Core.Module.TupleDispatch.Element} (table : CodeTable) (stack : Stack)
    (evaluated : evalTupleIn globals heap frame items = .ok (.tuple scalars)) :
    advanceIn table globals (.running heap frame (.ret (.tuple items)) stack) =
      some (none, .delivering heap stack (.ok (.tuple scalars))) := by
  simp [advanceIn, Operand.evalIn, evaluated]

end Silmaril.Languages.Python.Core.Closure.Executor
