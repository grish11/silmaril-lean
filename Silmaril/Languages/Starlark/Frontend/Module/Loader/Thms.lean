module

public import Silmaril.Languages.Starlark.Frontend.Module.Loader.Defs
public import Silmaril.Languages.Starlark.Modules.Loader.Thms

public section

namespace Silmaril.Languages.Starlark.Frontend.Module.Loader

/-- Agreement at the existing loader boundary for a prepared text graph. -/
theorem runs_iff_load (prepared : Prepared) (id : Modules.Loader.ModuleId)
    (session : Modules.Loader.Session) (out : Modules.Loader.Result Modules.Published) :
    Modules.Loader.Runs prepared.program prepared.manifest [] (.initialize id) session out ↔
      prepared.load id session = out :=
  Modules.Loader.runs_iff_denote prepared.program prepared.manifest [] (.initialize id) session out

end Silmaril.Languages.Starlark.Frontend.Module.Loader
