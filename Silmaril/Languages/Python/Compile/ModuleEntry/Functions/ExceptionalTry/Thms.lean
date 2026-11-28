module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry.Defs

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry

variable {state failure action : Type}

theorem afterCleanup_resume (pending : Outcome state failure) (reached : state) :
    pending.afterCleanup ⟨reached, .ok ()⟩ = ⟨reached, pending.completion⟩ := rfl

theorem afterCleanup_replace (pending : Outcome state failure) (reached : state) (error : failure) :
    pending.afterCleanup ⟨reached, .error error⟩ = ⟨reached, .error error⟩ := rfl

theorem runCleanup_enter_raised (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (reached : state) (error : failure) (cleanup : List action)
    (defined : isPythonError error = true) :
    runCleanup suite isPythonError ⟨reached, .error error⟩ cleanup =
      (Outcome.mk reached (.error error)).afterCleanup (suite reached cleanup) := by
  simp [runCleanup, Outcome.canEnterCleanup, defined]

theorem runCleanup_outside_profile (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (reached : state) (error : failure) (cleanup : List action)
    (outside : isPythonError error = false) :
    runCleanup suite isPythonError ⟨reached, .error error⟩ cleanup = ⟨reached, .error error⟩ := by
  simp [runCleanup, Outcome.canEnterCleanup, outside]

variable (testClass : state → failure → String → Except failure Bool)

theorem selectHandler_first_match (reached : state) (pending : failure) (name : String)
    (arm : List action) (target : Option String) (rest : List (Arm action)) (selected : testClass reached pending name = .ok true) :
    selectHandler testClass reached pending (.named name arm target :: rest) = .ok (some ⟨arm, target⟩) := by
  simp [selectHandler, selected]

theorem selectHandler_continue (reached : state) (pending : failure) (name : String)
    (arm : List action) (target : Option String) (rest : List (Arm action)) (skipped : testClass reached pending name = .ok false) :
    selectHandler testClass reached pending (.named name arm target :: rest) =
      selectHandler testClass reached pending rest := by
  simp [selectHandler, skipped]

theorem selectHandler_first_error (reached : state) (pending error : failure) (name : String)
    (arm : List action) (target : Option String) (rest : List (Arm action)) (failed : testClass reached pending name = .error error) :
    selectHandler testClass reached pending (.named name arm target :: rest) = .error error := by
  simp [selectHandler, failed]

variable (operations : HandlerOperations state failure)

theorem runHandler_target (suite : state → List action → Outcome state failure)
    (reached bound : state) (pending : failure) (name : String) (arm : List action)
    (boundTarget : operations.bindCaught reached name pending = .ok bound) :
    runHandler suite operations reached pending ⟨arm, some name⟩ =
      let handled := suite bound arm
      ⟨operations.unbind handled.reached name, handled.completion⟩ := by
  simp [runHandler, boundTarget]

theorem runHandler_binding_failed (suite : state → List action → Outcome state failure)
    (reached : state) (pending error : failure) (name : String) (arm : List action)
    (failed : operations.bindCaught reached name pending = .error error) :
    runHandler suite operations reached pending ⟨arm, some name⟩ = ⟨reached, .error error⟩ := by
  simp [runHandler, failed]

theorem run_unmatched (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (error : failure)
    (body otherwise cleanup : List action) (handlers : List (Arm action))
    (failed : suite initial body = ⟨reached, .error error⟩) (defined : isPythonError error = true)
    (unmatched : selectHandler operations.testClass reached error handlers = .ok none) :
    run suite isPythonError operations initial ⟨body, handlers, otherwise, cleanup⟩ =
      runCleanup suite isPythonError ⟨reached, .error error⟩ cleanup := by
  simp [run, afterBody, failed, defined, unmatched]

theorem run_selected (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (error : failure)
    (body otherwise cleanup : List action) (handlers : List (Arm action)) (arm : SelectedArm action)
    (failed : suite initial body = ⟨reached, .error error⟩) (defined : isPythonError error = true)
    (selected : selectHandler operations.testClass reached error handlers = .ok (some arm)) :
    run suite isPythonError operations initial ⟨body, handlers, otherwise, cleanup⟩ =
      runCleanup suite isPythonError (runHandler suite operations reached error arm) cleanup := by
  simp [run, afterBody, failed, defined, selected]

theorem run_handler_error (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (pending error : failure)
    (body otherwise cleanup : List action) (handlers : List (Arm action))
    (failed : suite initial body = ⟨reached, .error pending⟩) (defined : isPythonError pending = true)
    (selectionFailed : selectHandler operations.testClass reached pending handlers = .error error) :
    run suite isPythonError operations initial ⟨body, handlers, otherwise, cleanup⟩ =
      runCleanup suite isPythonError ⟨reached, .error error⟩ cleanup := by
  simp [run, afterBody, failed, defined, selectionFailed]

theorem run_outside_profile (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (error : failure)
    (body otherwise cleanup : List action) (handlers : List (Arm action))
    (failed : suite initial body = ⟨reached, .error error⟩) (outside : isPythonError error = false) :
    run suite isPythonError operations initial ⟨body, handlers, otherwise, cleanup⟩ = ⟨reached, .error error⟩ := by
  simp [run, afterBody, failed, outside, runCleanup_outside_profile]

theorem run_normal_body (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (body otherwise cleanup : List action)
    (handlers : List (Arm action)) (normal : suite initial body = ⟨reached, .ok ()⟩) :
    run suite isPythonError operations initial ⟨body, handlers, otherwise, cleanup⟩ =
      runCleanup suite isPythonError (suite reached otherwise) cleanup := by
  simp [run, afterBody, normal]

theorem matchClass_missing {Value : Type} (lookup : String → Option Value) (classOf : Value → HandlerClass)
    (actual : Core.Closure.ExceptionClass) (name : String) (missing : lookup name = none) :
    matchClass lookup classOf actual name = .error (some (.nameError name)) := by
  simp [matchClass, missing]

theorem matchClass_invalid {Value : Type} (lookup : String → Option Value) (classOf : Value → HandlerClass)
    (actual : Core.Closure.ExceptionClass) (name : String) {value : Value}
    (found : lookup name = some value) (invalid : classOf value = .invalid) :
    matchClass lookup classOf actual name = .error (some .invalidHandlerClass) := by
  simp [matchClass, found, invalid]

theorem matchClass_stock {Value : Type} (lookup : String → Option Value) (classOf : Value → HandlerClass)
    (actual : Core.Closure.ExceptionClass) (name : String) {value : Value} {expected : Core.Closure.ExceptionClass}
    (found : lookup name = some value) (stock : classOf value = .stock expected) :
    matchClass lookup classOf actual name = .ok (decide (expected.catches actual)) := by
  simp [matchClass, found, stock]


theorem RaiseName.error_missing {scope : Source.Scope} {Value : Type} (operand : RaiseName scope)
    (lookup : Source.Name → Option Value) (classify : Value → RaiseValue)
    (missing : lookup operand.name = none) :
    operand.error lookup classify = .nameError operand.name := by
  simp [RaiseName.error, missing]

theorem RaiseName.error_found {scope : Source.Scope} {Value : Type} (operand : RaiseName scope)
    (lookup : Source.Name → Option Value) (classify : Value → RaiseValue) {value : Value}
    (found : lookup operand.name = some value) :
    operand.error lookup classify = (classify value).normalize := by
  simp [RaiseName.error, found]

theorem RaiseValue.stock_empty_normalizes (kind : Core.Closure.ExceptionClass) :
    (RaiseValue.stockClass kind).construct .empty = some (RaiseValue.stockClass kind).normalize := rfl

theorem RaiseValue.instance_normalizes (value : Core.Closure.ExceptionInstance) :
    (RaiseValue.exceptionInstance value).normalize = .raisedInstance value := rfl

theorem RaiseValue.instance_notCallable (value : Core.Closure.ExceptionInstance) :
    (RaiseValue.exceptionInstance value).construct .empty = some .notCallable := rfl

theorem RaiseCall.error_missing {scope : Source.Scope} {Value : Type} (call : RaiseCall scope)
    (lookup : Source.Name → Option Value) (classify : Value → RaiseValue) (text? : Value → Option Core.Text)
    (missing : lookup call.name = none) :
    call.error lookup classify text? = some (.nameError call.name) := by
  simp [RaiseCall.error, missing]

theorem RaiseCall.error_argument {scope : Source.Scope} {Value : Type} (call : RaiseCall scope)
    (lookup : Source.Name → Option Value) (classify : Value → RaiseValue) (text? : Value → Option Core.Text)
    {callee : Value} {error : Core.Closure.RuntimeError}
    (found : lookup call.name = some callee) (failed : call.evalArguments lookup text? = .error error) :
    call.error lookup classify text? = some error := by
  simp [RaiseCall.error, found, failed]

theorem RaiseCall.error_construct {scope : Source.Scope} {Value : Type} (call : RaiseCall scope)
    (lookup : Source.Name → Option Value) (classify : Value → RaiseValue) (text? : Value → Option Core.Text)
    {callee : Value} {arguments : RaiseArguments}
    (found : lookup call.name = some callee) (read : call.evalArguments lookup text? = .ok arguments) :
    call.error lookup classify text? = (classify callee).construct arguments := by
  simp [RaiseCall.error, found, read]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry
