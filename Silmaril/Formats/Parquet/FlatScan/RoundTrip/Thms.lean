module

public import Silmaril.Formats.Parquet.FlatScan.Defs
public import Batteries.Data.List.Basic
import Silmaril.Proofs.Formats.Parquet.FlatScan.RoundTrip

/-! Composition laws for checked flat INT32 schema, columns and row groups. -/

public section

namespace Silmaril.Formats.Parquet.FlatScan

/-- A one-page PLAIN V1 chunk consumes just the given checked scalar result. -/
theorem scanColumn_singleV1 {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footerStart rows bodySize : Nat} {field : Field} {column : Footer.ColumnChunk}
    {span : Footer.Span} {frame : Page.Frame} {slots : List (Option Int32)}
    (rowBound : rows ≤ limits.maxRows) (pageBound : bodySize ≤ limits.maxPageBytes)
    (path : column.metadata.pathInSchema = [field.name]) (kind : column.metadata.physicalType = .int32)
    (count : column.metadata.numValues = (rows : Int)) (codec : column.metadata.codec = 0)
    (encodings : column.metadata.encodings = [0, 3])
    (dictionary : column.metadata.dictionaryPageOffset = none) (index : column.metadata.indexPageOffset = none)
    (located : Page.columnSpan footerStart column.metadata = some span)
    (framed : Page.readChunk limits.page source span = .ok [frame])
    (header : frame.value = ⟨bodySize, bodySize, none, .dataV1 ⟨rows, 0, 3, 3⟩⟩)
    (decoded : decoder field frame.value (Footer.fileBytes source frame.payload.start frame.payload.stop) = .ok slots)
    (length : slots.length = rows) (nonNull : field.layout = .required → slots.any Option.isNone = false) :
    ∃ result, scanColumn limits decoder source footerStart field rows column = .ok result ∧
      result.cells.toList = slots :=
  Proofs.Formats.Parquet.FlatScan.scanColumn_singleV1 rowBound pageBound path kind count codec encodings
    dictionary index located framed header decoded length nonNull

/-- A recovered one-group footer and successful column reads recover the
complete ordered row-group observation at file entry point zero. -/
theorem scanFileRowGroup_single {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footer : Footer.Span} {schema : List Footer.SchemaElement} {rows : Nat}
    {schemaFields : List Field} {chunks : List Footer.ColumnChunk} {totalSize : Int}
    {expected : List (Field × List (Option Int32))}
    (read : Footer.readFooter limits.footer source =
      .ok (footer, ⟨1, schema, rows, [⟨chunks, totalSize, rows, none, none⟩], none⟩))
    (schemaOk : flatSchema (ε := ε) limits schema = .ok schemaFields)
    (rowBound : rows ≤ limits.maxRows) (cellBound : rows * schemaFields.length ≤ limits.maxCells)
    (arity : schemaFields.length = chunks.length)
    (ready : List.Forall₂ (fun pair observation => pair.1 = observation.1 ∧
      ∃ cells, scanColumn limits decoder source footer.start pair.1 rows pair.2 = .ok cells ∧
        cells.cells.toList = observation.2) (schemaFields.zip chunks) expected) :
    ∃ batch, scanFileRowGroup limits decoder source 0 = .ok batch ∧ batch.rowCount = rows ∧
      batch.columns.map (fun (field, column) => (field, column.cells.toList)) = expected :=
  Proofs.Formats.Parquet.FlatScan.scanFileRowGroup_single read schemaOk rowBound cellBound arity ready

theorem rows_eq_fold (batch : Batch) :
    batch.rows = ((batch.columns.map fun (_, column) => column.cells.toList).foldl
      (List.zipWith fun row cell => cell :: row) (List.replicate batch.rowCount [])).map List.reverse :=
  Proofs.Formats.Parquet.FlatScan.rows_eq_fold batch

/-- The checked schema recovers the ordered required and optional fields of a
flat INT32 footer whose leaf names are unique. -/
theorem flatSchema_of_fields {ε : Type} {limits : Limits} (root : String) (fields : List Field)
    (bounded : fields.length ≤ limits.maxColumns) (unique : (fields.map (·.name)).Nodup) :
    flatSchema (ε := ε) limits
      (⟨none, none, none, root, some fields.length⟩ :: fields.map (fun field =>
        ⟨some .int32, none, some (if field.layout = .required then .required else .optional), field.name, none⟩)) =
      .ok fields :=
  Proofs.Formats.Parquet.FlatScan.flatSchema_of_fields root fields bounded unique

end Silmaril.Formats.Parquet.FlatScan
