module

public import Silmaril.Formats.Parquet.FlatScan.Defs
public import Batteries.Data.List.Basic
import all Silmaril.Formats.Parquet.FlatScan.Defs
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatScan

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatScan

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
      result.cells.toList = slots := by
  have page : checkPage (ε := ε) limits field frame.value true false [0, 3] = .ok (rows, none) := by
    simp [header, checkPage, admitsValueEncoding, Nat.not_lt.mpr pageBound, Pure.pure, Except.pure]
  have noNull : ¬ (field.layout = .required ∧ none ∈ slots) := by
    rintro ⟨required, present⟩
    have absent := List.any_eq_false.mp (nonNull required) none present
    exact absent rfl
  refine ⟨⟨slots.toArray, by simpa using length⟩, ?_, by simp⟩
  simp [scanColumn, scanColumnCore, frameColumn, admitsValueEncoding, readFrame, Nat.not_lt.mpr rowBound,
    path, kind, count, codec, encodings, dictionary, index, located, framed, page, decoded, length,
    noNull, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure, List.forIn_cons, List.forIn_nil]

private theorem scanColumns_from_values {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footerStart rows : Nat} {pairs : List (Field × Footer.ColumnChunk)}
    {expected : List (Field × List (Option Int32))}
    (ready : List.Forall₂ (fun pair observation => pair.1 = observation.1 ∧
      ∃ cells, scanColumn limits decoder source footerStart pair.1 rows pair.2 = .ok cells ∧
        cells.cells.toList = observation.2) pairs expected) :
    ∃ cols, scanColumns limits decoder source footerStart rows pairs = .ok cols ∧
      cols.map (fun (field, column) => (field, column.cells.toList)) = expected := by
  induction ready with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons head _ ih =>
    rename_i first observation pairs expected
    obtain ⟨same, cells, read, values⟩ := head
    obtain ⟨rest, reads, seen⟩ := ih
    refine ⟨(first.1, cells) :: rest, ?_, ?_⟩
    · simp [scanColumns, List.mapM_cons, Bind.bind, Except.bind, Pure.pure, Except.pure, read] at reads ⊢
      simp [reads, same]
    · simp [seen, values]

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
      batch.columns.map (fun (field, column) => (field, column.cells.toList)) = expected := by
  obtain ⟨cols, runs, seen⟩ := scanColumns_from_values ready
  refine ⟨⟨rows, cols⟩, ?_, rfl, seen⟩
  have nonnegative : ¬ ((rows : Int) < 0) := Int.not_lt.mpr (Int.natCast_nonneg rows)
  have capacity : rows * chunks.length ≤ limits.maxCells := by simpa [arity] using cellBound
  simp [scanFileRowGroup, read, scanRowGroup, schemaOk, Nat.not_lt.mpr rowBound, nonnegative, Nat.not_lt.mpr capacity,
    arity, runs, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem rows_eq_fold (batch : Batch) :
    batch.rows = ((batch.columns.map fun (_, column) => column.cells.toList).foldl
      (List.zipWith fun row cell => cell :: row) (List.replicate batch.rowCount [])).map List.reverse := by
  simp [Batch.rows, List.foldl_map]

/-- The checked schema recovers the ordered required and optional fields of a
flat INT32 footer whose leaf names are unique. -/
theorem flatSchema_of_fields {ε : Type} {limits : Limits} (root : String) (fields : List Field)
    (bounded : fields.length ≤ limits.maxColumns) (unique : (fields.map (·.name)).Nodup) :
    flatSchema (ε := ε) limits
      (⟨none, none, none, root, some fields.length⟩ :: fields.map (fun field =>
        ⟨some .int32, none, some (if field.layout = .required then .required else .optional), field.name, none⟩)) =
      .ok fields := by
  let leaf (field : Field) : Footer.SchemaElement :=
    ⟨some .int32, none, some (if field.layout = .required then .required else .optional), field.name, none⟩
  have round : ∀ field, flatField (ε := ε) (leaf field) = .ok field := by
    rintro ⟨name, layout⟩
    cases layout <;> rfl
  have mapped : (fields.map leaf).mapM (flatField (ε := ε)) = .ok fields := by
    clear bounded unique
    induction fields with
    | nil => rfl
    | cons field rest ih =>
      rw [List.map_cons, List.mapM_cons, round, ih]
      rfl
  have shape : flatSchema (ε := ε) limits
      (⟨none, none, none, root, some fields.length⟩ :: fields.map leaf) = .ok fields := by
    have count : (some (fields.length : Int) != some (Int.ofNat fields.length)) = false := by
      change (some (Int.ofNat fields.length) != some (Int.ofNat fields.length)) = false
      exact bne_self_eq_false _
    have exceptError (α : Type) (e : Error ε) : (throw e : Except (Error ε) α) = .error e := rfl
    unfold flatSchema
    simp only [List.length_map, Nat.not_lt.mpr bounded, ite_false, Bool.false_or, Option.isSome_none,
      bne_self_eq_false, Bool.false_and, count, Bool.false_eq_true, Bind.bind, Except.bind,
      exceptError, Pure.pure, Except.pure]
    simp [mapped, unique]
  exact shape

end Silmaril.Proofs.Formats.Parquet.FlatScan
