module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.NestedPoint.Multi.Thms
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.NestedPoint.Multi.Defs

namespace Silmaril.Formats.Parquet.NestedPoint.Multi

private def fixture : Bytes := ⟨include_bytes "../../../../../data/parquet-nested-multipage/unequal-cuts.parquet"⟩
private def singleton : Bytes := ⟨include_bytes "../../../../../data/parquet-nested-footer/optional-point.parquet"⟩

private def readFile (source : Bytes) (limits : Limits := {}) : Option (Except Error (List Row)) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  pure (read limits snapshot 0)

private def change (offset : Nat) (byte : UInt8) : Bytes :=
  Bytes.ofList (fixture.toList.set offset byte)

#guard readFile fixture = some (.ok [
  some (-100, some 4398046511104), some (-99, some 4398046511105), none,
  some (-97, none), some (-96, some 4398046511108), some (-95, some 4398046511109),
  some (-94, some 4398046511110), some (-93, some 4398046511111), some (-92, none),
  none, some (-90, some 4398046511114), some (-89, some 4398046511115)])

-- The last optional page now disagrees at rows 8 and 9, with identical value bytes and count.
#guard readFile (change 230 0xa4) = some (.error .parentPresence)
-- The last header advertises three slots instead of four.
#guard readFile (change 216 6) = some (.error (.column 1 (.rowCount 12 11)))
-- An added value state in the last page cannot draw bytes from another page.
#guard readFile (change 230 0xa2) = some (.error (.column 1 (.page 208 (.plain .truncated))))

#guard readFile fixture { maxRows := 11 } = some (.error (.column 0 .rowLimit))
#guard readFile fixture { maxChunkBytes := 100 } = some (.error (.column 1 .chunkLimit))
#guard readFile fixture { leaf := { framing := { maxPages := 3 } } } =
  some (.error (.column 1 (.framing .pageLimit)))

#guard readFile singleton = some (.ok [some (-7, some 4398046511104), none, some (0, none)])

private def singletonEntry (source : Bytes) : Option (Except NestedPoint.Error (List Row)) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  pure (NestedPoint.read {} snapshot 0)

#guard singletonEntry singleton = some (.ok [some (-7, some 4398046511104), none, some (0, none)])
#guard singletonEntry fixture = some (.error (.leaf 0 .pageCount))

end Silmaril.Formats.Parquet.NestedPoint.Multi
