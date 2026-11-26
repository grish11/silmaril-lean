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

theorem run_failed_body (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (error : failure)
    (body otherwise cleanup : List action) (failed : suite initial body = ⟨reached, .error error⟩) :
    run suite isPythonError initial ⟨body, none, otherwise, cleanup⟩ =
      runCleanup suite isPythonError ⟨reached, .error error⟩ cleanup := by
  simp [run, afterBody, failed]

theorem run_bare_handler (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (error : failure)
    (body handler otherwise cleanup : List action)
    (failed : suite initial body = ⟨reached, .error error⟩) (defined : isPythonError error = true) :
    run suite isPythonError initial ⟨body, some handler, otherwise, cleanup⟩ =
      runCleanup suite isPythonError (suite reached handler) cleanup := by
  simp [run, afterBody, failed, defined]

theorem run_bare_handler_outside_profile (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (error : failure)
    (body handler otherwise cleanup : List action)
    (failed : suite initial body = ⟨reached, .error error⟩) (outside : isPythonError error = false) :
    run suite isPythonError initial ⟨body, some handler, otherwise, cleanup⟩ = ⟨reached, .error error⟩ := by
  simp [run, afterBody, failed, outside, runCleanup_outside_profile]

theorem run_normal_body (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial reached : state) (body otherwise cleanup : List action)
    (handler : Option (List action)) (normal : suite initial body = ⟨reached, .ok ()⟩) :
    run suite isPythonError initial ⟨body, handler, otherwise, cleanup⟩ =
      runCleanup suite isPythonError (suite reached otherwise) cleanup := by
  simp [run, afterBody, normal]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry
