module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.NextPage

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

/-- Select the next page only from an accepted page. An attempted second
fill uses the actual backing and cache left by the first operation. -/
def fillFollowing {State : Type} (handler : Handler State) (first : Outcome State)
    (target : SlotId) (select : Bytes → Option Page) : Option (Outcome State) :=
  match first.result with
  | .error _ => none
  | .ok bytes => (select bytes).map (fill handler first.file first.cache target)

end Silmaril.Machine.SqliteVfs.PageRead.NextPage
