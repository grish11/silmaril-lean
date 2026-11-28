module

public import Silmaril.Formats.Parquet.RleBoolean.Defs
public import Mathlib.Data.List.Forall2
import Silmaril.Proofs.Formats.Parquet.RleBoolean.Correctness

/-! Exact selected frames, Boolean values, definition slots and row count. -/

public section

namespace Silmaril.Formats.Parquet.RleBoolean

/-- Recover the same-source framing and the exact length-prefixed value
stream for each page, in the order used by the returned nullable slots. -/
theorem readGroup_wire {limits : Limits} {source : Bytes} {name : String} {index : Nat}
    {slots : List (Option Bool)} (read : readGroup limits source name index = .ok slots) :
    ∃ snapshot root leaf group column chunk frames pages,
      Snapshot.check (Failure := Unit) limits.snapshot source = .ok snapshot ∧
      snapshot.metadata.schema = [root, leaf] ∧ IsOptionalBoolean leaf ∧ leaf.name = name ∧
      snapshot.groupAt index = some group ∧ group.columns = [column] ∧
      ColumnMatches leaf group column ∧ column.metadata.codec = 0 ∧
      Page.columnSpan snapshot.footer.start column.metadata = some chunk ∧
      Page.readChunk limits.framing snapshot.bytes chunk = .ok frames ∧
      List.Forall₂ (PageWire limits snapshot.bytes) frames pages ∧
      slots = pages.flatten ∧ slots.length = group.numRows.toNat :=
  Proofs.Formats.Parquet.RleBoolean.readGroup_wire read

end Silmaril.Formats.Parquet.RleBoolean
