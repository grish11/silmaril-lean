module

public import Silmaril.Formats.Parquet.Date.Leaf.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Date.Leaf.Binding

public section

namespace Silmaril.Formats.Parquet.Date.Leaf

/-- The checked leaf and the exact raw annotation use the same original ordinal. -/
theorem bind_exact {limits : Footer.Limits} {snapshot : Snapshot.Checked} {ordinal : Nat}
    {bound : Bound} (accepted : bind limits snapshot ordinal = .ok bound) :
    bound.snapshot = snapshot ∧ bound.ordinal = ordinal ∧ Date.IsDateLeaf bound.binding.leaf ∧
      ∃ selected, Footer.ColumnOrder.FlatWire limits snapshot ordinal selected ∧
        selected.leaf = bound.binding.leaf ∧
        Date.Internal.readAnnotation selected.selection.reader selected.selection.leaf.item.fields =
          .ok bound.binding.annotation :=
  Proofs.Formats.Parquet.Date.Leaf.bind_exact accepted

/-- Admission retains the strict checked snapshot of the supplied bytes. -/
theorem open_exact {limits : Snapshot.Limits} {source : Bytes} {ordinal : Nat} {bound : Bound}
    (opened : openLeaf limits source ordinal = .ok bound) :
    Snapshot.check (Failure := Unit) limits source = .ok bound.snapshot ∧
      bind limits.footer bound.snapshot ordinal = .ok bound :=
  Proofs.Formats.Parquet.Date.Leaf.open_exact opened

/-- The original group and physical column ordinals determine one in-file, disjoint chunk. -/
theorem selectChunk_exact {bound : Bound} {index : Nat} {chunk : Chunk}
    (selected : selectChunk bound index = .ok chunk) :
    bound.snapshot.groupAt index = some chunk.group ∧
      chunk.group.columns[bound.ordinal]? = some chunk.column ∧
      chunk.column.metadata.pathInSchema = [bound.binding.leaf.name] ∧
      chunk.column.metadata.physicalType = .int32 ∧
      Page.columnSpan bound.snapshot.footer.start chunk.column.metadata = some chunk.span ∧
      Internal.disjoint bound.snapshot index bound.ordinal chunk.span = true :=
  Proofs.Formats.Parquet.Date.Leaf.selectChunk_exact selected

/-- The exact bounded frames expose their signed nullable words in source order. -/
theorem readGroup_exact {limits : Date.Limits} {bound : Bound} {index : Nat} {slots : Slots}
    (read : readGroup limits bound index = .ok slots) :
    ∃ chunk frames pages, selectChunk bound index = .ok chunk ∧
      Page.readChunk limits.scan.page bound.snapshot.bytes chunk.span = .ok frames ∧
      Page.Chain chunk.span chunk.span.start chunk.span.stop frames ∧
      List.Forall₂ (PageWire limits.page bound) frames pages ∧
      slots = pages.flatten ∧ slots.length = chunk.group.numRows.toNat :=
  Proofs.Formats.Parquet.Date.Leaf.readGroup_exact read

/-- The frame consumes its original scalar bytes and validity levels. -/
theorem pageWire_exact {limits : ScalarPage.Limits} {bound : Bound} {frame : Page.Frame}
    {slots : Slots} (decoded : PageWire limits bound frame slots) :
    let body := Footer.fileBytes bound.snapshot.bytes frame.payload.start frame.payload.stop
    ∃ params layout prepared words, FlatScan.int32PageParameters bound.field frame.value = some params ∧
      ScalarPage.validate params limits body = .ok layout ∧
      ScalarPage.PreparedWire params limits layout body prepared ∧
      ScalarPage.Kind.int32.readPlain (prepared.mask.count true) prepared.scalars = .ok words ∧
      slots.map Option.isSome = prepared.mask ∧ slots.filterMap id = words :=
  Proofs.Formats.Parquet.Date.Leaf.pageWire_exact decoded

end Silmaril.Formats.Parquet.Date.Leaf
