module

public import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Defs
public import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs

/-! # Finite entry for the variadic binder -/

@[expose] public section
namespace Silmaril.Languages.Python.Core.Closure.Finite.Variadic

def enter (fn : Function) (parameters : Call.VariadicParameters fn.code.layout)
    (supplied : List Value) (heap : HeapTable) : Except Failure (Snapshot fn.code.layout) :=
  match Call.firstDangling fn heap.project with
  | some identity => .error (.danglingCell identity)
  | none =>
    (parameters.complete supplied).bind fun values =>
      Dispatch.enter fn parameters.destinations values heap

end Silmaril.Languages.Python.Core.Closure.Finite.Variadic
