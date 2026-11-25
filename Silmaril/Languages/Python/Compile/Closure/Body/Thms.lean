module

public import Silmaril.Languages.Python.Compile.Closure.Body.Defs
import Silmaril.Proofs.Languages.Python.Compile.Closure.Body.Arity
import Silmaril.Proofs.Languages.Python.Compile.Closure.Body.Paths

/-! # Call and parameter arity of lowered closure bodies -/

public section
namespace Silmaril.Languages.Python.Compile.Closure.Body

theorem ArgumentsTranslation.length {scope : Source.Scope} {sources targets}
    (translated : ArgumentsTranslation scope sources targets) : targets.length = sources.length :=
  Proofs.Languages.Python.Compile.Closure.Body.arguments_length translated

theorem TaggedArgumentsTranslation.length {scope : Source.Scope} {sources targets}
    (translated : TaggedArgumentsTranslation scope sources targets) : targets.length = sources.length :=
  Proofs.Languages.Python.Compile.Closure.Body.tagged_arguments_length translated

theorem Compiled.parameter_count {source : Source.Module} (compiled : Compiled source) :
    compiled.parameters.slots.length = compiled.declaration.length := by
  simpa using congrArg List.length compiled.parameterOrder

theorem Compiled.paths_distinct {source : Source.Module} (compiled : Compiled source) :
    compiled.paths.Nodup :=
  Proofs.Languages.Python.Compile.Closure.Body.paths_distinct compiled

end Silmaril.Languages.Python.Compile.Closure.Body
