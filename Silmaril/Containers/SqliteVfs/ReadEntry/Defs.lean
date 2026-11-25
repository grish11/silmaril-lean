module

public import Silmaril.Containers.SqliteVfs.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary.Defs

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.ReadEntry

open Silmaril.Machine
open Silmaril.Machine.SqliteVfs.PageRead.ReadBoundary (FileBinding)

/-- Project a singleton ABI handler-entry observation through an explicit file
binding. The projection describes a receive and carries no handler response. -/
def projectEntry (binding : FileBinding) (observation : SqliteRead.Obs) : Option Event :=
  match observation.trace, observation.ending with
  | [request], .returned .handlerEntry =>
    (binding request.file).map fun handle =>
      .recv (.read handle request.offset.toNat request.amount.toNat)
  | _, _ => none

end Silmaril.Containers.SqliteVfs.ReadEntry
