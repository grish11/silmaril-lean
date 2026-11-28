module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.NestedPoint.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.NestedPoint.Defs

namespace Silmaril.Formats.Parquet.NestedPoint

private def fixture : Bytes := ⟨include_bytes "../../../../data/parquet-nested-footer/optional-point.parquet"⟩
private def requiredParent : Bytes := ⟨include_bytes "../../../../data/parquet-nested-footer/required-parent.parquet"⟩

private def readFile (source : Bytes) (group : Nat := 0) (limits : Limits := {}) :
    Option (Except Error (List Row)) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  pure (read limits snapshot group)

private def replace (offset : Nat) (byte : UInt8) : Bytes :=
  Bytes.ofList (fixture.toList.set offset byte)

#guard readFile fixture = some (.ok [some (-7, some 4398046511104), none, some (0, none)])

-- Original optional packed levels [2,0,1] become [2,1,0]. The value count
-- and all page and chunk extents still match, but parent validity differs.
#guard readFile (replace 57 0x06) = some (.error .parentPresence)
-- Change the first optional level from 2 to 1. Parent validity still
-- matches, but the original INT64 word is now surplus.
#guard readFile (replace 57 0x11) = some (.error (.plain 1 .trailingBytes))
-- The second selected chunk advertises Snappy rather than UNCOMPRESSED.
#guard readFile (replace 325 2) = some (.error (.leaf 1 (.codec 1)))
#guard readFile (replace 57 0x13) = some (.error (.leaf 1 (.presence .definitionLevel)))
#guard readFile fixture 1 = some (.error (.leaf 0 (.metadata (.groupOrdinal 1))))
#guard readFile fixture 0 { presence := { maxBodyBytes := 14 } } = some (.error (.leaf 1 .bodyLimit))
#guard readFile requiredParent = some (.error (.leaf 0 (.metadata .unsupportedShape)))

end Silmaril.Formats.Parquet.NestedPoint
