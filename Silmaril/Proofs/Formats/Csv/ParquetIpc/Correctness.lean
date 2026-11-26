module

public import Silmaril.Formats.Csv.ParquetIpc.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Defs
import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Thms
import Silmaril.Formats.Parquet.Snapshot.FlatInt32.ToCsv.Thms
import Silmaril.Formats.Csv.EventStream.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms
import Silmaril.Formats.Csv.Typed.Utf8.Thms
import Silmaril.Formats.Arrow.FromCsv.Stream.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Csv.ParquetIpc

open Silmaril.Relational Silmaril.Formats
open Silmaril.Formats.Csv.ParquetIpc
open Silmaril.Formats.Parquet
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema codecs)

private theorem ofFn_inj {n : Nat} {α : Type*} {f g : Fin n → α}
    (equal : List.ofFn f = List.ofFn g) : f = g := by
  funext i
  have observed := congrArg (fun xs : List α => xs[i.val]?) equal
  simpa [List.getElem?_ofFn, i.isLt] using observed

private theorem schema_inj {α : Type*} {left right : PositionalSchema α}
    (equal : List.ofFn left.kind = List.ofFn right.kind) : left = right := by
  cases left with
  | mk n f =>
    cases right with
    | mk m g =>
      have width : n = m := by simpa using congrArg List.length equal
      subst m
      change List.ofFn f = List.ofFn g at equal
      rw [ofFn_inj equal]

private theorem ofFn_get_map {α β : Type*} (xs : List α) (f : α → β) :
    List.ofFn (fun (i : Fin xs.length) => f (xs.get i)) = xs.map f := by
  change List.ofFn (f ∘ xs.get) = _
  rw [← List.map_ofFn]
  exact congrArg (List.map f) (List.ofFn_getElem (xs := xs))

/-- These positions have the same CSV labels and codecs as the source schema,
with the Arrow kind and nullability recorded at every position. -/
private def ipcSchema (schema : Scan.Schema String Unit) : Csv.Typed.Schema Arrow.ToCsv.Kind :=
  ⟨schema.width, fun i => (((csvSchema schema).kind i).1, (.int32, true))⟩

private theorem ipcSchema_eq (schema : Scan.Schema String Unit) :
    Arrow.ToCsv.schemaOf (fields schema) = ipcSchema schema := by
  apply schema_inj
  change List.ofFn (fun i => Arrow.ToCsv.labelOf ((fields schema).get i)) = _
  rw [ofFn_get_map]
  simp [Arrow.ToCsv.labelOf, fields, ipcSchema, csvSchema, List.map_ofFn, Function.comp_def]

private def ipcRows (schema : Csv.Typed.Schema Arrow.ToCsv.Kind)
    (rows : Csv.Typed.Table schema Arrow.ToCsv.Cell) : List Arrow.Row :=
  rows.map fun row => List.ofFn fun i => Arrow.ToCsv.eraseCell (schema.kind i).2 (row i)

private theorem decode_ipc_rows (schema : Scan.Schema String Unit) (wire : Csv.Bytes) :
    (Csv.Typed.Utf8.decode (Arrow.ToCsv.schemaOf (fields schema)) Arrow.CsvUtf8.codecs wire).map
        (List.map (Arrow.ToCsv.eraseRow (fields schema))) =
      (Csv.Typed.Utf8.decode (csvSchema schema) codecs wire).map
        (List.map fun row => List.ofFn fun i => (row i).map Arrow.Value.int32) := by
  change (Csv.Typed.Utf8.decode (Arrow.ToCsv.schemaOf (fields schema)) Arrow.CsvUtf8.codecs wire).map
    (ipcRows (Arrow.ToCsv.schemaOf (fields schema))) = _
  rw [ipcSchema_eq]
  rfl

/-- The Parquet writer's slot fold accumulates each original row in reverse
column order before its final reversal. -/
private theorem fold_slots {n : Nat} (indices : List (Fin n))
    (rows : List (Fin n → Option Int32)) (initial : (Fin n → Option Int32) → List (Option Int32)) :
    (indices.map fun i => rows.map (· i)).foldl (List.zipWith fun row cell => cell :: row)
        (rows.map initial) =
      rows.map fun row => (indices.reverse.map row) ++ initial row := by
  induction indices generalizing initial with
  | nil => simp
  | cons i indices ih =>
    simp only [List.map_cons, List.foldl_cons, List.zipWith_map, List.zipWith_self]
    rw [ih]
    simp [List.reverse_cons, List.map_append]

private theorem writer_rows {schema : Scan.Schema String Unit}
    (rows : Csv.Typed.Table (csvSchema schema) Cell) :
    (FlatInt32Writer.FromCsv.writerInput schema rows).rows = rows.map List.ofFn := by
  change List (Fin schema.width → Option Int32) at rows
  unfold FlatInt32Writer.Input.rows FlatInt32Writer.FromCsv.writerInput FlatInt32Writer.rowsFromSlots
  simp only [List.map_ofFn, Function.comp_def, Parquet.PlainV1Writer.Input.slots]
  change ((List.ofFn (fun i : Fin schema.width => rows.map (· i))).foldl
      (List.zipWith fun row cell => cell :: row) (List.replicate rows.length [])).map List.reverse =
    rows.map (fun row => List.ofFn row)
  rw [show List.ofFn (fun i : Fin schema.width => rows.map (· i)) =
    (List.ofFn id).map (fun i => rows.map (· i)) by rw [List.map_ofFn]; rfl]
  rw [← List.map_const', fold_slots]
  simp [List.map_map, Function.comp_def, List.map_ofFn]

private theorem writer_schema {schema : Scan.Schema String Unit}
    (rows : Csv.Typed.Table (csvSchema schema) Cell) :
    (FlatInt32Writer.FromCsv.writerInput schema rows).arrowSchema = schema := by
  apply schema_inj
  change List.ofFn (fun i => (((FlatInt32Writer.FromCsv.writerInput schema rows).columns.get i).name, ())) = _
  rw [ofFn_get_map (FlatInt32Writer.FromCsv.writerInput schema rows).columns
    (fun col => (col.name, ()))]
  simp [FlatInt32Writer.FromCsv.writerInput, List.map_ofFn, Function.comp_def]

private theorem same_ipc_decode (schema : Scan.Schema String Unit) {left right : Csv.Bytes}
    (decoded : Csv.Typed.Utf8.decode (csvSchema schema) codecs left =
      Csv.Typed.Utf8.decode (csvSchema schema) codecs right) :
    Csv.Typed.Utf8.decode (Arrow.ToCsv.schemaOf (fields schema)) Arrow.CsvUtf8.codecs left =
      Csv.Typed.Utf8.decode (Arrow.ToCsv.schemaOf (fields schema)) Arrow.CsvUtf8.codecs right := by
  rw [ipcSchema_eq]
  exact decoded

private theorem rows_ofFn_inj {n : Nat} {left right : List (Fin n → Option Int32)}
    (same : left.map List.ofFn = right.map List.ofFn) : left = right := by
  exact (List.map_inj_right fun _ _ => ofFn_inj).mp same

private theorem writer_collect {schema : Scan.Schema String Unit} {limits : FlatInt32Writer.Limits}
    {rows : Csv.Typed.Table (csvSchema schema) Cell} {output : FlatInt32Writer.Encoded}
    (written : FlatInt32Writer.emit limits (FlatInt32Writer.FromCsv.writerInput schema rows) = .ok output) :
    let snapshot := limits.snapshotLimits (FlatInt32Writer.FromCsv.writerInput schema rows)
    (Snapshot.FlatInt32.ToCsv.readEvents snapshot schema output.bytes).collect =
      .ok ⟨⟨csvSchema schema, rows⟩, .eos⟩ := by
  dsimp only
  let snapshot := limits.snapshotLimits (FlatInt32Writer.FromCsv.writerInput schema rows)
  obtain ⟨openedRows, observed, _, opened⟩ := FlatInt32Writer.emit_snapshot_readAll written
  rw [writer_rows] at observed
  have normalized (readSchema : Scan.Schema String Unit)
      (readRows : List (Fin readSchema.width → Option Int32))
      (sameSchema : readSchema = schema)
      (sameRows : readRows.map (fun (row : Fin readSchema.width → Option Int32) => List.ofFn row) =
        rows.map (fun (row : Fin schema.width → Option Int32) => List.ofFn row))
      (read : Snapshot.FlatInt32.readAll snapshot readSchema output.bytes =
        .ok ⟨readSchema, ⟨[AlignedColumns.ofRows readRows], .eos⟩⟩) :
      (Snapshot.FlatInt32.ToCsv.readEvents snapshot schema output.bytes).collect =
        .ok ⟨⟨csvSchema schema, rows⟩, .eos⟩ := by
    subst readSchema
    rw [rows_ofFn_inj sameRows] at read
    have flattened : ([AlignedColumns.ofRows rows] : List (Scan.Columns (csvSchema schema) Cell)).flatMap
        AlignedColumns.toRows = rows := by
      change (AlignedColumns.ofRows rows).toRows ++ [] = rows
      rw [List.append_nil]
      exact AlignedColumns.toRows_ofRows rows
    simp only [Snapshot.FlatInt32.ToCsv.readEvents, read, Except.map, Arrow.Events.EventStream.collect,
      Arrow.Events.Trace.collect, Arrow.Events.Trace.rows]
    exact congrArg (fun table => Except.ok (Arrow.Events.Observation.mk ⟨csvSchema schema, table⟩ .eos))
      flattened
  exact normalized (FlatInt32Writer.FromCsv.writerInput schema rows).arrowSchema
    openedRows (writer_schema rows) observed opened

open Silmaril.Formats.Relational.NamedTable (Packed)

variable {Name : Type*} [DecidableEq Name]
variable {db : Packed Name Csv.Field Cell} {name : Name} {schema : Scan.Schema String Unit}
variable {limits : Limits} {wire : Csv.Bytes}

private theorem written_collect {written : FlatInt32Writer.FromCsv.Result Name}
    (parquet : FlatInt32Writer.FromCsv.convert db name schema limits.csv limits.parquet wire = .ok written)
    (matching : ∀ rows, Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows →
      limits.snapshot = limits.parquet.snapshotLimits (FlatInt32Writer.FromCsv.writerInput schema rows)) :
    db name = none ∧ ∃ rows : Csv.Typed.Table (csvSchema schema) Cell,
      Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows ∧
      (Snapshot.FlatInt32.ToCsv.readEvents limits.snapshot schema written.bytes).collect =
        .ok ⟨⟨csvSchema schema, rows⟩, .eos⟩ := by
  obtain ⟨vacant, rows, output, decoded, emitted, rfl⟩ := FlatInt32Writer.FromCsv.convert_written parquet
  exact ⟨vacant, rows, decoded, (matching rows decoded).symm ▸ writer_collect emitted⟩

theorem convert_of_admitted {written : FlatInt32Writer.FromCsv.Result Name} {ipc : KBytes}
    (parquet : FlatInt32Writer.FromCsv.convert db name schema limits.csv limits.parquet wire = .ok written)
    (matching : ∀ rows, Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows →
      limits.snapshot = limits.parquet.snapshotLimits (FlatInt32Writer.FromCsv.writerInput schema rows))
    (ipcAdmitted : Arrow.FromCsv.Stream.emitCsvUtf8 limits.ipc (fields schema) wire = .ok ipc) :
    ∃ result, convert db name schema limits wire = .ok result := by
  obtain ⟨vacant, rows, decoded, collected⟩ := written_collect parquet matching
  obtain ⟨exported, encoded, _⟩ :=
    Csv.Typed.Utf8.encode_of_decode (fun _ => Csv.Typed.Codecs.int32_printParse) decoded
  have exportOk : Snapshot.FlatInt32.ToCsv.convert db name schema limits.snapshot written.bytes =
      .ok ⟨Function.update db name (some ⟨csvSchema schema, rows⟩), csvSchema schema, exported⟩ :=
    (Csv.EventStream.convertCollected_ok_iff _).mpr ⟨vacant, rows, exported, collected, encoded, rfl⟩
  have roundTrip := Csv.Typed.Utf8.decode_encode (fun _ => Csv.Typed.Codecs.int32_parsePrint) encoded
  have ipcExport : Arrow.FromCsv.Stream.emitCsvUtf8 limits.ipc (fields schema) exported = .ok ipc := by
    have same := same_ipc_decode schema (roundTrip.trans decoded.symm)
    simpa only [Arrow.FromCsv.Stream.emitCsvUtf8, Arrow.FromCsv.Stream.ofCsvUtf8, same] using ipcAdmitted
  exact ⟨⟨Function.update db name (some ⟨csvSchema schema, rows⟩), written.bytes, exported, ipc⟩,
    by simp only [convert, parquet, exportOk, ipcExport]⟩

theorem convert_readback {result : Result Name}
    (converted : convert db name schema limits wire = .ok result)
    (matching : ∀ rows, Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows →
      limits.snapshot = limits.parquet.snapshotLimits (FlatInt32Writer.FromCsv.writerInput schema rows)) :
    db name = none ∧ ∃ rows : Csv.Typed.Table (csvSchema schema) Cell,
      Csv.Typed.Utf8.decode (csvSchema schema) codecs wire = .ok rows ∧
      result.db = Function.update db name (some ⟨csvSchema schema, rows⟩) ∧
      (Snapshot.FlatInt32.ToCsv.readEvents limits.snapshot schema result.parquet).collect =
        .ok ⟨⟨csvSchema schema, rows⟩, .eos⟩ ∧
      Csv.Typed.Utf8.decode (csvSchema schema) codecs result.csv = .ok rows ∧
      Arrow.readRows limits.ipc result.ipc =
        .ok ⟨fields schema, [rows.map fun row => List.ofFn fun i => (row i).map Arrow.Value.int32]⟩ := by
  cases parquet : FlatInt32Writer.FromCsv.convert db name schema limits.csv limits.parquet wire with
  | error reason => simp [convert, parquet] at converted
  | ok written =>
    obtain ⟨vacant, source, decoded, collected⟩ := written_collect parquet matching
    cases exportEq : Snapshot.FlatInt32.ToCsv.convert db name schema limits.snapshot written.bytes with
    | error reason => simp [convert, parquet, exportEq] at converted
    | ok exported =>
      cases ipcEq : Arrow.FromCsv.Stream.emitCsvUtf8 limits.ipc (fields schema) exported.wire with
      | error reason => simp [convert, parquet, exportEq, ipcEq] at converted
      | ok ipc =>
        simp only [convert, parquet, exportEq, ipcEq, Except.ok.injEq] at converted
        subst result
        obtain ⟨rows, read, _, parsed, named⟩ := Snapshot.FlatInt32.ToCsv.convert_roundTrip exportEq
        rw [collected] at read
        have sameRows : source = rows := eq_of_heq
          (Scan.Observation.mk.inj (congrArg Arrow.Events.Observation.table (Except.ok.inj read))).2
        subst rows
        obtain ⟨ipcTyped, ipcDecoded, ipcRead, _⟩ := Arrow.FromCsv.Stream.emitCsvUtf8_readback ipcEq
        have same := decode_ipc_rows schema exported.wire
        rw [ipcDecoded, parsed] at same
        simp only [Except.map, Except.ok.injEq] at same
        refine ⟨vacant, source, decoded, named, collected, parsed, ?_⟩
        rw [ipcRead, same]

end Silmaril.Proofs.Formats.Csv.ParquetIpc
