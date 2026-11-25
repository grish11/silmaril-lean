module

public import Silmaril.Languages.Python.Compile.Locals.Defs
public import Silmaril.Languages.Python.Core.Locals.Thms

public section
namespace Silmaril.Languages.Python.Compile.Locals

theorem address_iff (scope : Source.Scope) (name : Source.Name) :
    (address? scope name).isSome ↔ name ∈ localNames scope := by
  by_cases access : scope.access name = some .local <;>
    simp [address?, localNames, access, List.any_eq_true]

theorem Compiled.run_exact {source : Source.Module} (compiled : Compiled source) :
    let answer := compiled.code.eval (Core.Locals.Store.empty _)
    Core.Locals.run compiled.code compiled.code.budget =
      .stop (.finished answer.store answer.result) (.observed (.returned answer.result)) := by
  simpa only [Core.Locals.run, Core.Locals.State.enter_answer] using
    Core.Locals.run_exact (Core.Locals.State.enter (Core.Locals.Store.empty _) compiled.code)
      (Nat.le_of_eq (Core.Locals.State.enter_budget _ _))

end Silmaril.Languages.Python.Compile.Locals
