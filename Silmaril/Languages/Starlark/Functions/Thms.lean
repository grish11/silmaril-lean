module

public import Silmaril.Languages.Starlark.Functions.Denotation.Defs
public import Silmaril.Languages.Starlark.Functions.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Functions.Eval

public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow Suite denoteSuite)

/-- Lifting a collection suite gives precisely its existing total denotation. -/
theorem denote_total (program : Program) (available : List DeclarationId) (suite : Suite 0)
    (state : State) : denoteBody program available (.total suite) state = denoteSuite suite state := by
  rw [denoteBody]

/-- Exact adequacy for the strict core, including errors and the post-call store. -/
theorem exec_iff_denoteBody (program : Program) (available : List DeclarationId) (body : Body)
    (state : State) (out : Outcome Flow) :
    Exec program available state body out ↔ denoteBody program available body state = out :=
  ⟨Proofs.Languages.Starlark.Functions.denote_eq_of_exec,
    fun h => h ▸ Proofs.Languages.Starlark.Functions.exec_denote program available body state⟩

end Silmaril.Languages.Starlark.Functions
