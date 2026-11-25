module

public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Functions.Builtins.Eval

public section

namespace Silmaril.Languages.Starlark.Functions.Builtins

open Lists

/-- The built-in rules account for the exact value or error and final store. -/
theorem invokes_iff_invoke (state : State) (id : Builtin) (args : Actual) (out : Outcome Lists.Value) :
    Invokes state id args out ↔ invoke id args state = out :=
  ⟨Proofs.Languages.Starlark.Functions.Builtins.invoke_eq_of_invokes,
    fun h => h ▸ Proofs.Languages.Starlark.Functions.Builtins.invokes_invoke state id args⟩

end Silmaril.Languages.Starlark.Functions.Builtins
