module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Correspondence

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry

theorem global_reference {scope : Source.Scope} {name : Source.Name}
    (reference : GlobalReference scope name) : globalReference? scope name = some reference :=
  Proofs.Languages.Python.Compile.ModuleEntry.global_reference reference

theorem statements_complete {scope : Source.Scope} {source : List Source.Stmt} {actions : List (Action scope)}
    (translated : Translation scope source actions) : lowerStatements scope source = .ok ⟨actions, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.statements_complete translated

theorem check_complete {source : Source.Module} {tree : Source.ScopeTree}
    {actions : List (Action tree.scope)} (analyzed : Source.analyze source = .ok tree)
    (moduleScope : tree.scope.context.kind = .module_) (translated : Translation tree.scope source.body actions) :
    check source = .ok ⟨tree, analyzed, moduleScope, actions, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.check_complete analyzed moduleScope translated

end Silmaril.Languages.Python.Compile.ModuleEntry
