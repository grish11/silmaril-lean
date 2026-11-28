module

public import Silmaril.Formats.Parquet.FlatScan.Defs
import all Silmaril.Formats.Parquet.FlatScan.Defs

namespace Silmaril.Proofs.Formats.Parquet.FlatScan

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatScan

private theorem fold_rows_length {count : Nat} (columns : List (Field × ColumnValues count))
    (rows : List (List (Option Int32))) (sized : rows.length = count) :
    (columns.foldl (fun rows (_, column) =>
      List.zipWith (fun row cell => cell :: row) rows column.cells.toList) rows).length = count := by
  induction columns generalizing rows with
  | nil => exact sized
  | cons first rest ih =>
    apply ih
    simp [List.length_zipWith, sized, first.2.sized]

public theorem rows_length (batch : Batch) : batch.rows.length = batch.rowCount := by
  simp only [Batch.rows, List.length_map]
  exact fold_rows_length batch.columns _ (by simp)

private theorem mapM_length {α β ε : Type} (read : α → Except ε β)
    {xs : List α} {ys : List β} (parsed : xs.mapM read = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    rw [List.mapM_nil] at parsed
    cases parsed
    rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at parsed
    cases step : read x with
    | error e => simp [step, bind, Except.bind] at parsed
    | ok y =>
      cases rest : xs.mapM read with
      | error e => simp [step, rest, bind, Except.bind] at parsed
      | ok tail =>
        simp [step, rest, bind, Except.bind, pure, Except.pure] at parsed
        simp [← parsed, ih rest]

public theorem scanRowGroup_dimensions {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footerStart : Nat} {schema : List Footer.SchemaElement} {group : Footer.RowGroup}
    {batch : Batch} (parsed : scanRowGroup limits decoder source footerStart schema group = .ok batch) :
    batch.rows.length = group.numRows.toNat ∧ batch.columns.length = group.columns.length := by
  have arity (fields : List Field) (available : flatSchema (ε := ε) limits schema = .ok fields) :
      batch.rowCount = group.numRows.toNat ∧ batch.columns.length = group.columns.length := by
    by_cases negative : group.numRows < 0
    · simp [scanRowGroup, available, negative, bind, Except.bind] at parsed
    by_cases rows : limits.maxRows < group.numRows.toNat
    · simp [scanRowGroup, available, negative, rows, bind, Except.bind] at parsed
    by_cases cells : limits.maxCells < group.numRows.toNat * fields.length
    · simp [scanRowGroup, available, negative, rows, cells, bind, Except.bind] at parsed
    by_cases same : fields.length = group.columns.length
    · have cells' : ¬limits.maxCells < group.numRows.toNat * group.columns.length := by
        rwa [← same]
      cases decoded : scanColumns limits decoder source footerStart group.numRows.toNat (fields.zip group.columns) with
      | error e =>
        simp [scanRowGroup, available, negative, rows, cells', same, decoded, bind, Except.bind] at parsed
      | ok result =>
        simp [scanRowGroup, available, negative, rows, cells', same, decoded, bind, Except.bind,
          pure, Except.pure] at parsed
        subst batch
        unfold scanColumns at decoded
        exact ⟨rfl, by simpa [List.length_zip, same] using mapM_length _ decoded⟩
    · simp [scanRowGroup, available, negative, rows, cells, same, bind, Except.bind] at parsed
  cases prepared : flatSchema (ε := ε) limits schema with
  | error e => simp [scanRowGroup, prepared, bind, Except.bind] at parsed
  | ok fields =>
    obtain ⟨rows, columns⟩ := arity fields prepared
    exact ⟨(rows_length batch).trans rows, columns⟩

/-- Every assembled row has one cell per scanned column. -/
public theorem rows_width (batch : Batch) (row : List (Option Int32)) (present : row ∈ batch.rows) :
    row.length = batch.columns.length := by
  have width {count : Nat} (columns : List (Field × ColumnValues count))
      (rows : List (List (Option Int32))) (n : Nat)
      (sized : ∀ row ∈ rows, List.length row = n) :
      ∀ row ∈ columns.foldl (fun rows (_, column) =>
        List.zipWith (fun row cell => cell :: row) rows column.cells.toList) rows,
        row.length = n + columns.length := by
    induction columns generalizing rows n with
    | nil => simpa using sized
    | cons column columns ih =>
      change ∀ row ∈ columns.foldl _ (List.zipWith (fun row cell => cell :: row) rows
        column.2.cells.toList), row.length = n + (column :: columns).length
      have step : ∀ row ∈ List.zipWith (fun row cell => cell :: row) rows column.2.cells.toList,
          List.length row = n + 1 := by
        intro row mem
        obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp mem
        have inRows : index < rows.length := by
          simp only [List.length_zipWith] at bound
          exact Nat.lt_of_lt_of_le bound (Nat.min_le_left _ _)
        rw [List.getElem_zipWith, List.length_cons, sized rows[index] (List.getElem_mem inRows)]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih _ (n + 1) step
  rw [Batch.rows] at present
  obtain ⟨reversed, member, rfl⟩ := List.mem_map.mp present
  simpa using width batch.columns (List.replicate batch.rowCount []) 0 (by simp) reversed member

/-- Reuse a recovered footer when its version, row counts and group index
pass the file-level checks. -/
public theorem scanFileRowGroup_of_footer {ε : Type} {limits : Limits} {decoder : DecodePage ε}
    {source : Bytes} {footer : Footer.Span} {metadata : Footer.Metadata} {index : Nat}
    {group : Footer.RowGroup}
    (read : Footer.readFooter limits.footer source = .ok (footer, metadata))
    (version : metadata.version = 1 ∨ metadata.version = 2)
    (counts : (metadata.rowGroups.all fun group => 0 ≤ group.numRows) = true)
    (total : (metadata.rowGroups.map (·.numRows)).sum = metadata.numRows)
    (found : metadata.rowGroups[index]? = some group) :
    scanFileRowGroup limits decoder source index =
      scanRowGroup limits decoder source footer.start metadata.schema group := by
  rcases version with version | version <;>
    simp [scanFileRowGroup, read, version, counts, total, found, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Proofs.Formats.Parquet.FlatScan
