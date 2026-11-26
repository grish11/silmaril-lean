module

public import Silmaril.Languages.Python.Core.Closure.Call.Variadic.Finite.Defs
public import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Core.Closure.Call.Variadic

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Finite

theorem enter_project {Continuation : Layout → Type} (fn : Function)
    (parameters : Call.VariadicParameters fn.code.layout) (supplied : List Value)
    (heap : HeapTable) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    (Finite.Variadic.enter fn parameters supplied heap).map
      (fun environment => ⟨environment.project, caller :: stack⟩) =
      parameters.enter fn supplied heap.project caller stack := by
  unfold Finite.Variadic.enter Call.VariadicParameters.enter
  cases Call.firstDangling fn heap.project with
  | some identity => rfl
  | none =>
    cases parameters.complete supplied with
    | error failure => rfl
    | ok arguments => exact Dispatch.enter_project fn parameters.destinations arguments heap caller stack

end Silmaril.Proofs.Languages.Python.Core.Closure.Call.Variadic
