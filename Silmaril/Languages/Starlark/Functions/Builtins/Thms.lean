module

public import Silmaril.Languages.Starlark.Functions.Builtins.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Functions.Builtins.Eval

public section

namespace Silmaril.Languages.Starlark.Functions.Builtins

open Lists
open Lists.Iteration (Cursor finishState)

/-- Cursor rules agree with the exact reached truth tests, result or error, and state. -/
theorem truthScans_iff_truthCursor (stop : Bool) (cursor : Cursor) (state : State) (out : Outcome Lists.Value) :
    TruthScans stop cursor state out ↔ truthCursor stop cursor state = out :=
  ⟨Proofs.Languages.Starlark.Functions.Builtins.truthCursor_eq_of_scans,
    fun h => h ▸ Proofs.Languages.Starlark.Functions.Builtins.scans_truthCursor stop cursor state⟩

/-- The quantifiers preserve the entire state reached by operand evaluation, even on error. -/
theorem quantify_finishState (id : Builtin) (stop : Bool) (state : State) (value : Lists.Value) :
    finishState (quantify id stop value state) = state :=
  Proofs.Languages.Starlark.Functions.Builtins.quantify_finishState id stop state value

/-- The built-in rules account for the exact value or error and final store. -/
theorem invokes_iff_invoke (state : State) (id : Builtin) (args : Actual) (out : Outcome Lists.Value) :
    Invokes state id args out ↔ invoke id args state = out :=
  ⟨Proofs.Languages.Starlark.Functions.Builtins.invoke_eq_of_invokes,
    fun h => h ▸ Proofs.Languages.Starlark.Functions.Builtins.invokes_invoke state id args⟩

end Silmaril.Languages.Starlark.Functions.Builtins
