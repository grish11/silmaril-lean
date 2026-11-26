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
  simp [evalTupleIn, assembleFlatTuple, Except.map, read, Except.bind]

theorem tuple_ordered {values : List Value} {scalars : List Core.Module.Value}
    (reads : items.mapM (TupleItem.evalIn globals heap frame) = .ok values)
    (checked : values.mapM Value.scalar? = some scalars) :
    evalTupleIn globals heap frame items = .ok (.tuple scalars) := by
  simp [evalTupleIn, assembleFlatTuple, Except.map, reads, checked, Except.bind]

theorem tuple_nonScalar {values : List Value}
    (reads : items.mapM (TupleItem.evalIn globals heap frame) = .ok values)
    (outside : values.mapM Value.scalar? = none) :
    evalTupleIn globals heap frame items = .error .unsupportedTupleElement := by
  simp [evalTupleIn, assembleFlatTuple, Except.map, reads, outside, Except.bind]

theorem tuple_return {scalars : List Core.Module.Value} (table : CodeTable) (stack : Stack)
    (evaluated : evalTupleIn globals heap frame items = .ok (.tuple scalars)) :
    advanceIn table globals (.running heap frame (.ret (.tuple items)) stack) =
      some (none, .delivering heap stack (.ok (.tuple scalars))) := by
  simp [advanceIn, Operand.evalIn, evaluated]

end Silmaril.Languages.Python.Core.Closure.Executor
