module

public import Silmaril.Formats.Parquet.FloatByteStreamSplit.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Parquet.FloatByteStreamSplit.Correctness

/-! Same-snapshot group selection, frame order, and exact nullable FLOAT words. -/

public section

namespace Silmaril.Formats.Parquet.FloatByteStreamSplit

/-- Success accounts for the selected footer column, every original frame
and its ordered bit slots, and the exact advertised row count. -/
theorem readGroup_wire {limits : Limits} {source : Bytes} {name : String} {index : Nat}
    {slots : List (Option UInt32)} (read : readGroup limits source name index = .ok slots) :
    ∃ snapshot root leaf group column chunk frames pages,
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
      snapshot.metadata.schema = [root, leaf] ∧ IsFlatFloat root leaf ∧ leaf.name = name ∧
      snapshot.groupAt index = some group ∧ group.columns = [column] ∧
      column.metadata.pathInSchema = [leaf.name] ∧ column.metadata.physicalType = .float ∧
      column.metadata.codec = 0 ∧ column.metadata.numValues = group.numRows ∧
      Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
      Page.readChunk limits.framing snapshot.bytes chunk = .ok frames ∧
      List.Forall₂ (PageWire limits snapshot.bytes) frames pages ∧
      slots = pages.flatten ∧ slots.length = group.numRows.toNat :=
  Proofs.Formats.Parquet.FloatByteStreamSplit.readGroup_wire read

end Silmaril.Formats.Parquet.FloatByteStreamSplit
