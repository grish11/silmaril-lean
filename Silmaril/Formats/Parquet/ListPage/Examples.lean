module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.ListPage.Thms
import Silmaril.Formats.Parquet.Page.Defs
import Silmaril.Formats.Parquet.Snapshot.Defs
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.ListPage.Defs
meta import Silmaril.Formats.Parquet.Page.Defs
meta import Silmaril.Formats.Parquet.Snapshot.Defs

namespace Silmaril.Formats.Parquet.ListPage

private def fixture : Bytes := ⟨include_bytes "../../../../data/parquet-list-v1/nullable-int32.parquet"⟩

-- The pinned Thrift oracle independently checks the canonical LIST annotation.
-- The selected group has a single chunk and one complete page.
private def readFixture (source : Bytes) (expectedRows : Option Nat := none) (limits : Limits := {}) :
    Option (Except Error (List Row)) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  let group ← snapshot.groupAt 0
  let [chunk] := group.columns | none
  if chunk.metadata.pathInSchema ≠ ["items", "list", "element"] then none else do
    let span ← Page.columnSpan snapshot.footer.start chunk.metadata
    let [frame] ← (Page.readChunk {} snapshot.bytes span).toOption | none
    let body ← snapshot.bytes.slice? frame.payload.start (some frame.payload.stop)
    pure (decodeV1 limits chunk.metadata.codec frame.value (expectedRows.getD group.numRows.toNat) body)

private def change (source : Bytes) (offset : Nat) (value : UInt8) : Bytes :=
  Bytes.ofList (source.toList.set offset value)

#guard readFixture fixture = some (.ok [
  none, some [], some [none], some [some (-7), none, some 0], some [some 9, none]])
#guard readFixture fixture (some 4) = some (.error (.rowCount 4 5))
#guard readFixture (change fixture 12 18) = some (.error (.repetition .truncated))

-- Nonzero repetition at the start is illegal, even for a well-typed element.
#guard readFixture (change (change fixture 26 0xb1) 32 0xe6) =
  some (.error .continuationWithoutList)
-- Repetition one has no meaning on an empty-list marker.
#guard readFixture (change fixture 26 0xb2) = some (.error .levelPair)
-- A null element can continue a nonempty list, but not an empty one.
#guard readFixture (change fixture 26 0xb4) = some (.error .continuationWithoutList)
#guard readFixture (change fixture 32 0xa4) = some (.error (.plain .trailingBytes))
#guard readFixture (change fixture 27 64) = some (.error (.definitionSection .truncatedDefinitions))
#guard readFixture fixture none { maxRows := 4 } = some (.error .rowLimit)
#guard readFixture fixture none { maxBodyBytes := 24 } = some (.error .bodyLimit)
#guard readFixture fixture none { levels := ⟨7, 16⟩ } = some (.error (.repetition .valueLimit))
#guard decodeV1 {} 1 ⟨0, 0, none, .dataV1 ⟨0, 0, 3, 3⟩⟩ 0 Bytes.empty = .error (.codec 1)
#guard decodeV1 {} 0 ⟨0, 0, some 0, .dataV1 ⟨0, 0, 3, 3⟩⟩ 0 Bytes.empty = .error .crc
#guard decodeV1 {} 0 ⟨0, 1, none, .dataV1 ⟨0, 0, 3, 3⟩⟩ 0 Bytes.empty = .error .bodySize
#guard decodeV1 {} 0 ⟨0, 0, none, .dataV1 ⟨0, 0, 4, 3⟩⟩ 0 Bytes.empty = .error .encoding

end Silmaril.Formats.Parquet.ListPage
