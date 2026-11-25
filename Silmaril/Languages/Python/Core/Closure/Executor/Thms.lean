module

public import Silmaril.Languages.Python.Core.Closure.Executor.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Executor.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Closure.Executor

theorem step_iff {table : CodeTable} {source target : State} {label : Option Event} :
    Step table source label target ↔ advance table source = some (label, target) :=
  ⟨Proofs.Languages.Python.Core.Closure.Executor.advance_of_step,
    Proofs.Languages.Python.Core.Closure.Executor.step_of_advance⟩

theorem step_deterministic {table : CodeTable} {source left right : State} {a b : Option Event}
    (first : Step table source a left) (second : Step table source b right) : (a, left) = (b, right) :=
  Option.some.inj ((step_iff.mp first).symm.trans (step_iff.mp second))

theorem run_path (table : CodeTable) (fuel : Nat) (source : State) :
    (labelled table).Path source (runPrefix table fuel source).1 (runPrefix table fuel source).2 :=
  Proofs.Languages.Python.Core.Closure.Executor.run_path table fuel source

/-- Return and defined-error delivery recover the exact suspended frame,
continuation and older stack with the residual heap. -/
theorem delivers_saved (table : CodeTable) (residual : Heap) (caller : Call.Saved Continuation)
    (older : Stack) (result : Result) :
    advance table (.delivering residual (caller :: older) result) =
      some (some (.resume result), .receiving residual caller older result) := rfl

end Silmaril.Languages.Python.Core.Closure.Executor
