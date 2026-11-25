module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions

theorem Positional.length {scope : Source.Scope} {sources targets}
    (translated : Positional scope sources targets) : targets.length = sources.length :=
  match translated with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ (Positional.length tail)

theorem global_read_resolved {scope : Source.Scope} {name : Source.Name}
    (global : Compile.Closure.Body.GlobalRead scope name) :
    scope.access name = some .implicitGlobal ∨ scope.access name = some .declaredGlobal :=
  match global with
  | .implicit access => Or.inl access
  | .declared access => Or.inr access

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions
