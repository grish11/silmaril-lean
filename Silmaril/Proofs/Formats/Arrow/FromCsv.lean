module

public import Silmaril.Formats.Arrow.FromCsv.Defs
import Silmaril.Formats.Arrow.Writer.Thms
import Silmaril.Formats.Relational.NamedTable.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.FromCsv

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Relational.NamedTable (Packed schemaMatches_eq_true_iff)
open Silmaril.Formats.Arrow.FromCsv
open Silmaril.Formats.Arrow.ToCsv (Kind Cell schemaOf eraseCell eraseRow codecs)

private theorem columnValues_type (kind : Kind) (cells : List (Option (Cell kind))) :
    (columnValues kind cells).type = kind.1 := by
  rcases kind with ⟨type, nullable⟩
  cases type <;> rfl

private theorem columnValues_observe (kind : Kind) (cells : List (Option (Cell kind))) :
    (columnValues kind cells).observe = cells.map (eraseCell kind) := by
  rcases kind with ⟨type, nullable⟩
  cases type <;> rfl

private theorem transpose_cons {α β : Type} (head : α → β) (tail : α → List β)
    (rows : List α) :
    List.zipWith List.cons (rows.map head) (rows.map tail) = rows.map (fun row => head row :: tail row) := by
  induction rows <;> simp_all

private theorem columns_preserve (fields : List Field) (rows : Scan.Table (schemaOf fields) Cell) :
    let columns := List.zipWith
      (fun (field : Field) values => (⟨field.name, field.nullable, values⟩ : Writer.NamedColumn)) fields
      (List.ofFn fun i : Fin fields.length =>
        columnValues ((schemaOf fields).kind i).2 (rows.map (fun row => row i)))
    columns.map Writer.NamedColumn.field = fields ∧
      Body.rowsOfColumns rows.length (columns.map fun column => column.values.observe) =
        rows.map (eraseRow fields) := by
  induction fields with
  | nil =>
    change [] = [] ∧ List.replicate rows.length [] = rows.map (fun _ => [])
    simp
  | cons field fields ih =>
    let tail : Scan.Table (schemaOf fields) Cell := rows.map fun row => fun i => row i.succ
    let values := List.ofFn fun i : Fin fields.length =>
      columnValues ((schemaOf fields).kind i).2 (tail.map (fun row => row i))
    let head : Scan.Row (schemaOf (field :: fields)) Cell → Option (Cell (field.type, field.nullable)) :=
      fun row => row (0 : Fin (fields.length + 1))
    let first := columnValues (field.type, field.nullable) (rows.map head)
    have valuesCons : (List.ofFn fun i : Fin (field :: fields).length =>
        columnValues ((schemaOf (field :: fields)).kind i).2 (rows.map (fun row => row i))) =
        first :: values := by
      rw [List.ofFn_succ]
      congr 1
      apply congrArg List.ofFn
      funext i
      change columnValues ((schemaOf fields).kind i).2 (rows.map (fun row => row i.succ)) =
        columnValues ((schemaOf fields).kind i).2 (tail.map (fun row => row i))
      apply congrArg (columnValues ((schemaOf fields).kind i).2)
      symm
      exact (List.map_map (g := fun (row : Scan.Row (schemaOf fields) Cell) => row i)
        (f := fun (row : Scan.Row (schemaOf (field :: fields)) Cell) j => row j.succ))
    rw [valuesCons]
    let column : Writer.NamedColumn := ⟨field.name, field.nullable, first⟩
    let columns := List.zipWith
      (fun (field : Field) values => (⟨field.name, field.nullable, values⟩ : Writer.NamedColumn)) fields values
    change (column :: columns).map Writer.NamedColumn.field = field :: fields ∧
      Body.rowsOfColumns rows.length (column.values.observe :: columns.map (fun c => c.values.observe)) = _
    have h := ih tail
    change columns.map Writer.NamedColumn.field = fields ∧
      Body.rowsOfColumns tail.length (columns.map (fun c => c.values.observe)) = _ at h
    constructor
    · rw [List.map_cons, h.1]
      change Field.mk field.name field.nullable first.type :: fields = field :: fields
      rw [columnValues_type]
    · have rest := h.2
      rw [show tail.length = rows.length from List.length_map _] at rest
      change List.zipWith List.cons first.observe
        (Body.rowsOfColumns rows.length (columns.map (fun c => c.values.observe))) = _
      rw [rest, columnValues_observe]
      rw [List.map_map]
      have tailMap : List.map (eraseRow fields) tail =
          rows.map (fun row => eraseRow fields (fun i => row i.succ)) := List.map_map
      rw [tailMap, transpose_cons]
      congr 1
      funext row
      exact (List.ofFn_succ (f := fun i : Fin (fields.length + 1) =>
        eraseCell ((schemaOf (field :: fields)).kind i).2 (row i))).symm

theorem ofRows_preserves {fields : List Field} {rows : Scan.Table (schemaOf fields) Cell}
    {input : Writer.BatchInput} (checked : ofRows fields rows = .ok input) :
    input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) := by
  simp only [ofRows, ofObservation, schemaMatches_eq_true_iff, ite_true, AlignedColumns.ofRows] at checked
  let columns := List.zipWith
    (fun (field : Field) values => (⟨field.name, field.nullable, values⟩ : Writer.NamedColumn)) fields
    (List.ofFn fun i : Fin fields.length =>
      columnValues ((schemaOf fields).kind i).2 (rows.map (fun row => row i)))
  change (if columns.any (fun column => !column.nullable && column.values.nullCount != 0) then
    Except.error AdapterError.requiredNull else Except.ok ⟨rows.length, columns⟩) =
      Except.ok input at checked
  split at checked
  · cases checked
  · have made := Except.ok.inj checked
    subst input
    exact ⟨(columns_preserve fields rows).1, rfl, (columns_preserve fields rows).2⟩

theorem ofCsv_preserves {fields : List Field} {wire : Csv.Bytes} {input : Writer.BatchInput}
    (checked : ofCsv fields wire = .ok input) :
    ∃ rows : Scan.Table (schemaOf fields) Cell,
      Csv.Typed.decode (schemaOf fields) codecs wire = .ok rows ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) := by
  cases decoded : Csv.Typed.decode (schemaOf fields) codecs wire with
  | error error => simp [ofCsv, decoded, Except.mapError, Bind.bind, Except.bind] at checked
  | ok rows =>
    exact ⟨rows, rfl, ofRows_preserves (by
      simpa [ofCsv, decoded, Except.mapError, Bind.bind, Except.bind] using checked)⟩

theorem ofNamed_preserves {Name : Type} {db : Packed Name Csv.Field Cell} {name : Name}
    {fields : List Field} {input : Writer.BatchInput} (checked : ofNamed db name fields = .ok input) :
    ∃ rows : Scan.Table (schemaOf fields) Cell,
      Scan.observePacked db name = some ⟨schemaOf fields, rows⟩ ∧
      input.fields = fields ∧ input.rowCount = rows.length ∧ input.observe = rows.map (eraseRow fields) := by
  cases found : Scan.observePacked db name with
  | none => simp [ofNamed, found] at checked
  | some table =>
    rcases table with ⟨schema, rows⟩
    by_cases equal : schemaOf fields = schema
    · subst schema
      exact ⟨rows, rfl, ofRows_preserves (by simpa [ofNamed, found, ofRows] using checked)⟩
    · simp [ofNamed, found, ofObservation, schemaMatches_eq_true_iff, equal] at checked

end Silmaril.Proofs.Formats.Arrow.FromCsv
