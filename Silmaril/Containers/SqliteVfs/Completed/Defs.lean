module

public import Silmaril.Containers.SqliteVfs.Defs

@[expose] public section

namespace Silmaril.Containers.SqliteVfs.Completed

open Silmaril.Machine.SqliteVfs

/-- Read completed dependent exchanges from logical container events.
The execution relation accounts for the receive and any unanswered request. -/
def completed (events : List Event) : Trace :=
  events.filterMap fun
    | .recv _ => none
    | .send exchange => some exchange

end Silmaril.Containers.SqliteVfs.Completed
