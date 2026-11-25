module

public import Silmaril.Languages.Starlark.Modules.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Init

public section

namespace Silmaril.Languages.Starlark.Modules

open Functions (Program)
open Lists (State)

/-- Exact adequacy of validation, initialization, imports and publication. -/
theorem initializes_iff_initialize (program : Program) (host : Catalog) (source : Source)
    (caller : State) (out : Result Published) :
    Initializes program host source caller out ↔ initializeModule program host source caller = out :=
  ⟨Proofs.Languages.Starlark.Modules.eq_initialize_of_initializes,
    fun h => h ▸ Proofs.Languages.Starlark.Modules.initializes_initialize program host source caller⟩

end Silmaril.Languages.Starlark.Modules
