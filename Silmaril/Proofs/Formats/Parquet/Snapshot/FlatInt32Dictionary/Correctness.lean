module

public import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Defs
public import Batteries.Data.List.Basic
import Silmaril.Formats.Parquet.FlatScan.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Mathlib.Data.List.Forall2

public section

namespace Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Arrow Silmaril.Relational
open Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)

private theorem bind_ok {ε α β : Type} {input : Except ε α} {f : α → Except ε β} {out : β}
    (success : (input >>= f) = .ok out) : ∃ a, input = .ok a ∧ f a = .ok out := by
  cases input with
  | error _ => cases success
  | ok a => exact ⟨a, rfl, success⟩

private theorem mapError_ok {ε δ α : Type} {input : Except ε α} {f : ε → δ} {out : α}
    (success : input.mapError f = .ok out) : input = .ok out := by
  cases input with
  | error _ => cases success
  | ok _ => cases success; rfl

private theorem mapM_order {ε α β : Type} (f : α → Except ε β) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      List.Forall₂ (fun x y => f x = .ok y) xs ys
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
    rw [List.mapM_cons] at h
    obtain ⟨_, head, h⟩ := bind_ok h
    obtain ⟨_, tail, h⟩ := bind_ok h
    cases h
    exact .cons head (mapM_order f tail)

theorem readColumn_dispatch {limits : Limits} {source : Bytes} {footerStart rows : Nat}
    {field : FlatScan.Field} {column : Footer.ColumnChunk} {values : FlatScan.ColumnValues rows}
    (decoded : Internal.readColumn limits source footerStart field rows column = .ok values) :
    column.metadata.pathInSchema = [field.name] ∧ column.metadata.physicalType = .int32 ∧
    column.metadata.numValues = (rows : Int) ∧ column.metadata.codec = 0 ∧
    match column.metadata.dictionaryPageOffset with
    | none => FlatScan.scanColumn limits.plain.groups (FlatScan.decodeInt32Page limits.plain.pages)
        source footerStart field rows column = .ok values
    | some _ => DictionaryChunk.scanColumn limits.dictionary source footerStart field rows column.metadata =
        .ok values.cells.toList := by
  unfold Internal.readColumn at decoded
  dsimp only at decoded
  split at decoded <;> try contradiction
  rename_i path
  split at decoded <;> try contradiction
  rename_i kind
  split at decoded <;> try contradiction
  rename_i count
  split at decoded <;> try contradiction
  rename_i codec
  simp only [ne_eq, not_not] at path kind count codec
  refine ⟨path, kind, count, codec, ?_⟩
  cases offset : column.metadata.dictionaryPageOffset with
  | none =>
    rw [offset] at decoded
    exact mapError_ok decoded
  | some _ =>
    rw [offset] at decoded
    obtain ⟨slots, scanned, decoded⟩ := bind_ok decoded
    split at decoded <;> try contradiction
    cases decoded
    simpa using mapError_ok scanned

private theorem field_result {limits : Limits} {source : Bytes} {footerStart rows : Nat}
    {item : (FlatScan.Field × Footer.ColumnChunk) × Nat} {result : FlatScan.Field × FlatScan.ColumnValues rows}
    (decoded : Internal.readField limits source footerStart rows item = .ok result) :
    result.1 = item.1.1 ∧ Internal.readColumn limits source footerStart item.1.1 rows item.1.2 = .ok result.2 := by
  rcases item with ⟨⟨field, column⟩, index⟩
  unfold Internal.readField at decoded
  have mapped := mapError_ok decoded
  cases h : Internal.readColumn limits source footerStart field rows column with
  | error _ => simp [h, Except.map] at mapped
  | ok cells =>
    rw [h] at mapped
    cases mapped
    exact ⟨rfl, rfl⟩

private theorem field_order {limits : Limits} {source : Bytes} {footerStart rows : Nat}
    {items : List ((FlatScan.Field × Footer.ColumnChunk) × Nat)}
    {columns : List (FlatScan.Field × FlatScan.ColumnValues rows)}
    (rel : List.Forall₂ (fun item result => Internal.readField limits source footerStart rows item = .ok result)
      items columns) : columns.map Prod.fst = items.map (fun item => item.1.1) := by
  induction rel with
  | nil => rfl
  | cons head _ ih => simp [(field_result head).1, ih]

theorem scanGroup_ordered {limits : Limits} {source : Bytes} {footerStart : Nat}
    {fields : List FlatScan.Field} {group : Footer.RowGroup} {batch : FlatScan.Batch}
    (decoded : Internal.scanGroup limits source footerStart fields group = .ok batch) :
    batch.rows.length = group.numRows.toNat ∧ batch.columns.map Prod.fst = fields ∧
    List.Forall₂ (fun item (result : FlatScan.Field × FlatScan.ColumnValues batch.rowCount) =>
      result.1 = item.1.1 ∧
      Internal.readColumn limits source footerStart item.1.1 batch.rowCount item.1.2 = .ok result.2)
      (fields.zip group.columns).zipIdx batch.columns := by
  unfold Internal.scanGroup at decoded
  dsimp only at decoded
  split at decoded <;> try contradiction
  split at decoded <;> try contradiction
  split at decoded <;> try contradiction
  rename_i arity
  obtain ⟨columns, checked, decoded⟩ := bind_ok decoded
  cases decoded
  have ordered := mapM_order _ checked
  simp only [ne_eq, not_not] at arity
  refine ⟨FlatScan.rows_length _, ?_, ordered.imp (fun _ _ h => field_result h)⟩
  calc
    columns.map Prod.fst = (fields.zip group.columns).zipIdx.map (fun item => item.1.1) := field_order ordered
    _ = (fields.zip group.columns).map Prod.fst := by
      change List.map (Prod.fst ∘ Prod.fst) (List.zipIdx (fields.zip group.columns)) = _
      rw [← List.map_map, List.zipIdx_map_fst]
    _ = fields := List.map_fst_zip (Nat.le_of_eq arity)

private theorem typedRow_cells {schema : Scan.Schema String Unit} {values : List (Option Int32)}
    {row : Scan.Row schema Cell} (typed : Internal.typedRow schema values = .ok row) :
    List.ofFn row = values := by
  unfold Internal.typedRow at typed
  split at typed <;> try contradiction
  rename_i width
  cases typed
  apply List.ext_getElem
  · simp [width]
  · intro index left right
    simp

theorem decodeGroup_rows {limits : Limits} {schema : Scan.Schema String Unit}
    {fields : List FlatScan.Field} {snapshot : Snapshot.Checked} {index : Nat}
    {group : Footer.RowGroup} {rows : Reader.RowGroup schema Cell}
    (decoded : Internal.decodeGroup limits schema fields snapshot index group = .ok rows) :
    ∃ batch, Internal.scanGroup limits snapshot.bytes snapshot.footer.start fields group = .ok batch ∧
      rows.map (fun row => List.ofFn (fun i : Fin schema.width => row i)) = batch.rows ∧
      rows.length = group.numRows.toNat := by
  obtain ⟨batch, scanned, typed⟩ := bind_ok decoded
  have ordered := mapM_order _ typed
  have equal : rows.map (fun row => List.ofFn (fun i : Fin schema.width => row i)) = batch.rows := by
    clear decoded typed scanned
    generalize batch.rows = physical at ordered ⊢
    induction ordered with
    | nil => rfl
    | cons head _ ih => simp [typedRow_cells head, ih]
  exact ⟨batch, scanned, equal, by
    simpa using (congrArg List.length equal).trans (scanGroup_ordered scanned).1⟩

theorem readAll_of_openSource {limits : Limits} {schema : Scan.Schema String Unit} {bytes : Bytes}
    {snapshot : Snapshot.Checked} {decode : Snapshot.DecodeGroup schema Cell Error}
    (size : bytes.length ≤ limits.maxFileBytes)
    (opened : Snapshot.openSource limits.plain.snapshot (bind limits schema) bytes = .ok (snapshot.source decode)) :
    Snapshot.FlatInt32Dictionary.readAll limits schema bytes = snapshot.readAll decode := by
  simp [Snapshot.FlatInt32Dictionary.readAll, Nat.not_lt.mpr size, Snapshot.readAll,
    opened, Snapshot.Checked.readAll, Except.map]

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
    (Snapshot.FlatInt32Dictionary.readAll limits schema bytes).collect =
      .ok ⟨⟨schema, groups.flatten⟩, .readError (.decode index (.column columnIndex field reason))⟩ := by
  rw [readAll_of_openSource size opened]
  apply Snapshot.Checked.collect_readAll_first_error snapshot decode before after index groups _ split earlier
  simp [Snapshot.Checked.readGroup, located, failed]

end Silmaril.Proofs.Formats.Parquet.Snapshot.FlatInt32Dictionary
