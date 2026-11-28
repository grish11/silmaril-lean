module

public import Silmaril.Formats.Parquet.OffsetIndex.Defs
import Silmaril.Proofs.Formats.Parquet.OffsetIndex.Correctness

/-! Exact index extent, same-snapshot page binding and the ordered row partition. -/

public section

namespace Silmaril.Formats.Parquet.OffsetIndex

theorem readExact_ok_iff {limits : Limits} {bytes : Bytes} {locations : List Location} :
    readExact limits bytes = .ok locations ↔ readPrefix limits bytes = .ok (locations, bytes.length) :=
  Proofs.Formats.Parquet.OffsetIndex.readExact_ok_iff

theorem readPrefix_stop {limits : Limits} {bytes : Bytes} {locations : List Location}
    {next : Nat} (h : readPrefix limits bytes = .ok (locations, next)) :
    ∃ stop, next = stop + 1 ∧ bytes.data[stop]? = some 0 :=
  Proofs.Formats.Parquet.OffsetIndex.readPrefix_stop h

theorem matchPages_sound {groupRows : Nat} {locations : List Location} {frames : List Page.Frame}
    {entries : List Entry} (h : matchPages groupRows locations frames = .ok entries) :
    entries.map Entry.location = locations ∧ entries.map Entry.frame = frames ∧
      Partition 0 groupRows entries :=
  Proofs.Formats.Parquet.OffsetIndex.matchPages_sound h

/-- Bind the exact footer-advertised index and ordered page frames to the
same immutable snapshot and selected group and column ordinals. -/
theorem validate_present {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} {result : Index}
    (h : validate limits snapshot g c = .ok (some result)) :
    ∃ group column chunk bytes, Evidence limits snapshot g c result group column chunk bytes :=
  Proofs.Formats.Parquet.OffsetIndex.validate_present h

theorem validate_absent_iff {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat} :
    validate limits snapshot g c = .ok none ↔ ∃ group column,
      select limits snapshot g c = .ok (group, column) ∧
      column.offsetIndexOffset = none ∧ column.offsetIndexLength = none :=
  Proofs.Formats.Parquet.OffsetIndex.validate_absent_iff

theorem readFile_ok_iff {limits : Limits} {source : Bytes} {group column : Nat}
    {result : Option Index} :
    readFile limits source group column = .ok result ↔ source.length ≤ limits.maxFileBytes ∧
      ∃ snapshot, Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
        validate limits snapshot group column = .ok result :=
  Proofs.Formats.Parquet.OffsetIndex.readFile_ok_iff

/-- The indexed compressed size includes the serialized header and the
original compressed payload advertised by that header. -/
theorem Evidence.pageGeometry {limits : Limits} {snapshot : Snapshot.Checked} {g c : Nat}
    {result : Index} {group : Footer.RowGroup} {column : Footer.ColumnChunk}
    {chunk : Footer.Span} {bytes : Bytes}
    (h : Evidence limits snapshot g c result group column chunk bytes)
    {entry : Entry} (member : entry ∈ result.pages) :
    entry.location.offset = entry.frame.header.start ∧
      entry.location.compressedSize =
        (entry.frame.header.stop - entry.frame.header.start) + entry.frame.value.compressedSize :=
  Proofs.Formats.Parquet.OffsetIndex.evidence_pageGeometry h member

theorem Partition.ordered {start stop : Nat} {pages : List Entry} (h : Partition start stop pages) :
    pages.Pairwise (fun first second =>
      first.rowStop ≤ second.location.firstRow ∧ first.location.firstRow < second.location.firstRow) :=
  Proofs.Formats.Parquet.OffsetIndex.partition_ordered h

/-- Every row in the half-open group interval has exactly one indexed page.
Rows outside that interval have none. -/
theorem Partition.rowMultiplicity {start stop : Nat} {pages : List Entry}
    (h : Partition start stop pages) (row : Nat) :
    pages.countP (fun entry => decide (entry.location.firstRow ≤ row ∧ row < entry.rowStop)) =
      if start ≤ row ∧ row < stop then 1 else 0 :=
  Proofs.Formats.Parquet.OffsetIndex.partition_rowMultiplicity h row

end Silmaril.Formats.Parquet.OffsetIndex
