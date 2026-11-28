module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.Correctness

/-! Physical dispatch, ordered readback, and indexed errors for dictionary snapshots. -/

public section

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary

open Silmaril.Relational Silmaril.Formats.Arrow
open FlatInt32 (Cell)

/-- An admitted column matches the INT32 field, declared count and uncompressed
codec. Its result comes from the one reader selected by the dictionary offset. -/
theorem readColumn_dispatch {limits : Limits} {source : Bytes} {footerStart rows : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnChunk} {values : FlatScan.ColumnValues rows}
    (decoded : Internal.readColumn limits source footerStart field rows column = .ok values) :
    column.metadata.pathInSchema = [field.name] ∧ column.metadata.physicalType = .int32 ∧
    column.metadata.numValues = (rows : Int) ∧ column.metadata.codec = 0 ∧
    match column.metadata.dictionaryPageOffset with
    | none => FlatScan.scanColumn limits.plain.groups (FlatScan.decodeInt32Page limits.plain.pages)
        source footerStart field rows column = .ok values
    | some _ => DictionaryChunk.scanColumn limits.dictionary source footerStart field rows column.metadata =
        .ok values.cells.toList :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.readColumn_dispatch decoded

/-- Successful assembly reads each schema column exactly once, in order,
and recovers the declared number of rows. -/
theorem scanGroup_ordered {limits : Limits} {source : Bytes} {footerStart : Nat}
    {fields : List FlatScan.Field} {group : Footer.RowGroup} {batch : FlatScan.Batch}
    (decoded : Internal.scanGroup limits source footerStart fields group = .ok batch) :
    batch.rows.length = group.numRows.toNat ∧ batch.columns.map Prod.fst = fields ∧
    List.Forall₂ (fun item (result : FlatScan.Field × FlatScan.ColumnValues batch.rowCount) =>
      result.1 = item.1.1 ∧
      Internal.readColumn limits source footerStart item.1.1 batch.rowCount item.1.2 = .ok result.2)
      (fields.zip group.columns).zipIdx batch.columns :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.scanGroup_ordered decoded

/-- The typed rows passed to Arrow retain every assembled cell and row position. -/
theorem decodeGroup_rows {limits : Limits} {schema : Scan.Schema String Unit}
    {fields : List FlatScan.Field} {snapshot : Snapshot.Checked} {index : Nat}
    {group : Footer.RowGroup} {rows : Reader.RowGroup schema Cell}
    (decoded : Internal.decodeGroup limits schema fields snapshot index group = .ok rows) :
    ∃ batch, Internal.scanGroup limits snapshot.bytes snapshot.footer.start fields group = .ok batch ∧
      rows.map (fun row => List.ofFn (fun i : Fin schema.width => row i)) = batch.rows ∧
      rows.length = group.numRows.toNat :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.decodeGroup_rows decoded

/-- Once the bounded input opens, the exact event stream is the checked
snapshot's indexed read, including the original batch boundaries. -/
theorem readAll_of_openSource {limits : Limits} {schema : Scan.Schema String Unit} {bytes : Bytes}
    {snapshot : Snapshot.Checked} {decode : Snapshot.DecodeGroup schema Cell Error}
    (size : bytes.length ≤ limits.maxFileBytes)
    (opened : Snapshot.openSource limits.plain.snapshot (bind limits schema) bytes = .ok (snapshot.source decode)) :
    readAll limits schema bytes = snapshot.readAll decode :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.readAll_of_openSource size opened

/-- A column failure in the first failed group preserves exactly the earlier
complete rows and carries both original ordinals in its terminal error. -/
theorem collect_first_column_error {limits : Limits} {schema : Scan.Schema String Unit} {bytes : Bytes}
    {snapshot : Snapshot.Checked} {decode : Snapshot.DecodeGroup schema Cell Error}
    (size : bytes.length ≤ limits.maxFileBytes)
    (opened : Snapshot.openSource limits.plain.snapshot (bind limits schema) bytes = .ok (snapshot.source decode))
    {before after : List Nat} {index columnIndex : Nat} {field : String} {reason : ColumnError}
    {group : Footer.RowGroup} {groups : List (Reader.RowGroup schema Cell)}
    (split : List.range snapshot.groupCount = before ++ index :: after)
    (earlier : before.mapM (snapshot.readGroup decode) = .ok groups)
    (located : snapshot.groupAt index = some group)
    (failed : decode snapshot index group = .error (.column columnIndex field reason)) :
    (readAll limits schema bytes).collect =
      .ok ⟨⟨schema, groups.flatten⟩, .readError (.decode index (.column columnIndex field reason))⟩ :=
  Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary.collect_first_column_error
    size opened split earlier located failed

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary
