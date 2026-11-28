module

public import Silmaril.Formats.Parquet.ColumnIndex.Signed.Defs
import Silmaril.Proofs.Formats.Parquet.ColumnIndex.Signed.Correctness

/-! Signed statistics for the original decoded pages and original read errors. -/

public section

namespace Silmaril.Formats.Parquet.ColumnIndex.Signed

theorem checkOrder_sound {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩}
    (h : checkOrder limits snapshot binding = .ok ()) : SignedOrder limits snapshot binding :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.checkOrder_sound h

theorem checkPage_sound {claim : Claim} {count : Option Int} {slots : Slots}
    {bounds : Option Bounds} (h : checkPage claim count slots = .ok bounds) :
    PageValid claim count slots bounds :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.checkPage_sound h

theorem checkEach_sound {count : Nat → Option Int} {ordinal : Nat} {claims : List Claim}
    {pages : List Slots} {bounds : List (Option Bounds)}
    (h : checkEach count ordinal claims pages = .ok bounds) :
    PagesValid count ordinal claims pages bounds :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.checkEach_sound h

theorem ordered_iff {order : BoundaryOrder} {values : List Int} :
    ordered order values = true ↔ Ordered order values :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.ordered_iff

theorem declaredCount_eq (index : Index) (page : Nat) :
    declaredCount index page = index.raw.nullCounts.bind (·[page]?) :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.declaredCount_eq index page

theorem check_sound {index : Index} {pages : List Slots} {bounds : List (Option Bounds)}
    (h : check index pages = .ok bounds) : Verified index pages bounds :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.check_sound h

theorem splitPages_eq {decode : FlatColumn.DecodePage Int32 FlatScan.AdapterError}
    {leaf : Footer.SchemaElement} {metadata : Footer.ColumnMetadata} {source : Silmaril.Formats.Bytes}
    {start stop : Nat} {entries : List OffsetIndex.Entry} {pages : List Slots}
    (partition : OffsetIndex.Partition start stop entries)
    (original : List.Forall₂ (FlatColumn.CallbackWire decode leaf metadata source)
      (entries.map OffsetIndex.Entry.frame) pages) :
    splitPages entries pages.flatten = pages :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.splitPages_eq partition original

theorem read_error_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩} {group : Nat}
    {reason : FlatColumn.Error FlatScan.AdapterError} :
    read limits binding group = .error reason ↔ readFull limits binding group = .error reason :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.read_error_iff

theorem read_ok_iff {limits : Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩} {group : Nat}
    {result : Result} :
    read limits binding group = .ok result ↔
      readFull limits binding group = .ok result.rows ∧
      result.index = diagnose limits binding group result.rows :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.read_ok_iff

theorem read_verified {limits : Limits} {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    {binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩} {group : Nat}
    {result : Result} {bounds : List (Option Bounds)}
    (readOk : read limits binding group = .ok result) (verified : result.index = .ok (some bounds)) :
    ∃ index selected column chunk offsetBytes bytes pages,
      ColumnIndex.Evidence limits.indexFraming snapshot group binding.columnOrdinal
        index selected column chunk offsetBytes bytes ∧
      SignedOrder limits.index.offsetIndex.snapshot.footer snapshot binding ∧
      List.Forall₂ (FlatColumn.CallbackWire (decodePage limits.scalar layout) binding.leaf
        column.metadata snapshot.bytes) (index.offsetIndex.pages.map OffsetIndex.Entry.frame) pages ∧
      result.rows = pages.flatten ∧ Verified index pages bounds :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.read_verified readOk verified

end Silmaril.Formats.Parquet.ColumnIndex.Signed
