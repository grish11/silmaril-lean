module

public import Silmaril.Machine.SqliteVfs.PageRead.Defs

@[expose] public section

namespace Silmaril.Machine.SqliteVfs.PageRead.Release

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.PageRead

inductive ReleaseError where
  | unavailableSlot
  | pageMismatch
  deriving DecidableEq, Repr

/-- Release the expected resident page in one caller-owned slot. This
operation updates only the cache and retains ownership of the vacant slot. -/
def release (cache : Cache) (target : SlotId) (expected : Page) : Except ReleaseError Cache :=
  match cache target with
  | some (.resident resident _) =>
    if resident = expected then
      .ok (fun slot => if slot = target then some .vacant else cache slot)
    else .error .pageMismatch
  | _ => .error .unavailableSlot

end Silmaril.Machine.SqliteVfs.PageRead.Release
