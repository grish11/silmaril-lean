module

public import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Finite.Dispatch.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Closure.Finite.Dispatch

open Semantics.Operational

variable {Body Continuation : Layout → Type} {layout : Layout}

/-- A runtime code table has a finite presentation exactly when its
defined entries are supported by a finite key list. -/
theorem CodeRows.exists_project_iff (table : Closure.Dispatch.CodeTable Body) :
    (∃ rows : CodeRows Body, rows.project = table) ↔ ∃ keys, Environment.SupportedBy table keys :=
  Proofs.Languages.Python.Core.Closure.Finite.Dispatch.exists_codeRows_project_iff table

theorem freshFrame_project (fn : Function) (heap : HeapTable) :
    (freshFrame fn heap).project = fn.freshFrame heap.project :=
  Proofs.Languages.Python.Core.Closure.Finite.Dispatch.freshFrame_project fn heap

theorem writeArguments_project (writes : List (ParameterSlot layout × Value)) (before : Snapshot layout) :
    (writeArguments writes before).map Snapshot.project = Call.writeArguments writes before.project :=
  Proofs.Languages.Python.Core.Closure.Finite.Dispatch.writeArguments_project writes before

theorem bindPositional_project (parameters : Parameters layout) (arguments : List Value)
    (before : Snapshot layout) :
    (bindPositional parameters arguments before).map Snapshot.project =
      Call.bindPositional parameters arguments before.project :=
  Proofs.Languages.Python.Core.Closure.Finite.Dispatch.bindPositional_project parameters arguments before

theorem enter_project (fn : Function) (parameters : Parameters fn.code.layout) (arguments : List Value)
    (heap : HeapTable) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    (enter fn parameters arguments heap).map
      (fun environment => ⟨environment.project, caller :: stack⟩) =
      Call.enter fn parameters arguments heap.project caller stack :=
  Proofs.Languages.Python.Core.Closure.Finite.Dispatch.enter_project fn parameters arguments heap caller stack

/-- Match checked lookup and positional binding, including their exact
failures and the saved caller in a successful result. -/
theorem dispatch_project (rows : CodeRows Body) (callee : Value) (arguments : List Value)
    (heap : HeapTable) (caller : Call.Saved Continuation) (stack : List (Call.Saved Continuation)) :
    (dispatch rows callee arguments heap caller stack).map Active.project =
      Closure.Dispatch.dispatch rows.project callee arguments heap.project caller stack :=
  Proofs.Languages.Python.Core.Closure.Finite.Dispatch.dispatch_project rows callee arguments heap caller stack

theorem finish_project (heap : HeapTable) (stack : List (Call.Saved Continuation)) (result : Result) :
    (finish heap stack result).project = Call.finish heap.project stack result :=
  Proofs.Languages.Python.Core.Closure.Finite.Dispatch.finish_project heap stack result

theorem finish_resume (residual : HeapTable) (caller : Call.Saved Continuation)
    (older : List (Call.Saved Continuation)) (result : Result) :
    finish residual (caller :: older) result = ⟨residual, older, .resume caller result⟩ := rfl

end Silmaril.Languages.Python.Core.Closure.Finite.Dispatch
