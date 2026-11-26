module

public import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Finite.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Call.Variadic.Finite

public section
namespace Silmaril.Languages.Python.Core.Closure.Finite.Variadic

theorem enter_project {Continuation : Layout → Type} (fn : Function)
    (parameters : Call.VariadicParameters fn.code.layout) (supplied : List Value)
    (heap : HeapTable) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    (enter fn parameters supplied heap).map (fun environment => ⟨environment.project, caller :: stack⟩) =
      parameters.enter fn supplied heap.project caller stack :=
  Proofs.Languages.Python.Core.Closure.Call.Variadic.enter_project fn parameters supplied heap caller stack

end Silmaril.Languages.Python.Core.Closure.Finite.Variadic
