module

public import Silmaril.Formats.Arrow.Body.Defs
import Silmaril.Prelude.Bytes.Thms
import Init.Data.List.Nat.TakeDrop
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow

open Silmaril.Formats.Arrow Silmaril.Formats.Arrow.Body

theorem validAt_iff (bitmap : KBytes) (wf : bitmap.wf = true) (index : Nat) (valid : Bool) :
    validAt bitmap index = some valid ↔
      if bitmap.toList.isEmpty then valid = true
      else ∃ byte, bitmap.toList[index / 8]? = some byte ∧
        valid = byte.toNat.testBit (index % 8) := by
  have hlen := KBytes.length_toList bitmap wf
  cases bits : bitmap.toList with
  | nil =>
    have empty : bitmap.len = 0 := by simpa [bits] using hlen.symm
    simp [validAt, empty, eq_comm]
  | cons byte bytes =>
    have nonempty : bitmap.len ≠ 0 := by simp [bits] at hlen; omega
    rw [validAt, ite_eq_right nonempty, KBytes.get?_eq bitmap wf, bits]
    cases (byte :: bytes)[index / 8]? <;> simp [eq_comm]

theorem offsetAt_iff (offsets : KBytes) (index value : Nat) :
    offsetAt offsets index = some value ↔
      offsets.readLE (4 * index) 4 = some value ∧ value < 2^31 := by
  unfold offsetAt
  cases read : offsets.readLE (4 * index) 4 with
  | none => simp
  | some word =>
    by_cases fits : word < 2^31
    · simp [fits]
      rintro rfl
      exact fits
    · simp [fits]
      rintro rfl
      omega

theorem readCell_iff (buffers : ColumnBuffers) (index : Nat) (value : Option Value) :
    readCell buffers index = .ok value ↔ CellWire buffers index value := by
  unfold readCell CellWire
  cases bit : validAt buffers.validity index with
  | none => simp
  | some valid =>
    cases buffers with
    | int32 bitmap values =>
      simp only [ColumnBuffers.validity] at bit ⊢
      cases values.readLE (4 * index) 4 <;>
        cases valid <;> simp_all [pure, Except.pure] <;> exact eq_comm
    | utf8 bitmap offsets data =>
      simp only [ColumnBuffers.validity] at bit ⊢
      cases offsetAt offsets index with
      | none => simp
      | some lo =>
        cases offsetAt offsets (index + 1) with
        | none => simp
        | some hi =>
          by_cases bounded : lo ≤ hi ∧ hi ≤ data.len
          · cases valid with
            | false => simp [bounded.1, bounded.2, eq_comm, pure, Except.pure]
            | true =>
              cases utf8 : String.fromUTF8? (data.slice lo (hi - lo)).toByteArray <;>
                simp [bounded.1, bounded.2, utf8, eq_comm, pure, Except.pure]
          · simp [bounded, Bind.bind, Except.bind, ← and_assoc]
            intro hlo hhi
            exact (bounded ⟨hlo, hhi⟩).elim

private theorem mapCells_iff (buffers : ColumnBuffers) (indices : List Nat) (values : Column) :
    indices.mapM (readCell buffers) = .ok values ↔ CellsWire buffers indices values := by
  induction indices generalizing values with
  | nil => cases values <;> simp [CellsWire, pure, Except.pure]
  | cons index indices ih =>
    rw [List.mapM_cons]
    cases cell : readCell buffers index with
    | error reason =>
      cases values with
      | nil => simp [CellsWire, Bind.bind, Except.bind]
      | cons value values =>
        simp [CellsWire, ← readCell_iff, cell, Bind.bind, Except.bind]
    | ok value =>
      cases tail : indices.mapM (readCell buffers) <;>
        cases values <;> simp [CellsWire, ← readCell_iff, ← ih, cell, tail, Bind.bind,
          Except.bind, pure, Except.pure]

theorem readColumn_iff (node : FieldNode) (buffers : ColumnBuffers) (values : Column) :
    readColumn node buffers = .ok values ↔ ColumnWire node buffers values := by
  by_cases bitmap : BitmapExtent buffers.validity node.length
  · by_cases payload : PayloadExtent buffers node.length
    · cases mapped : (List.range node.length).mapM (readCell buffers) with
      | error reason =>
        simp [readColumn, ColumnWire, bitmap, payload, ← mapCells_iff, mapped, Bind.bind,
          Except.bind]
      | ok read =>
        by_cases count : read.countP Option.isNone = node.nullCount
        · simp [readColumn, ColumnWire, bitmap, payload, ← mapCells_iff, mapped, count,
            Bind.bind, Except.bind, pure, Except.pure]
          rintro rfl
          exact count
        · simp [readColumn, ColumnWire, bitmap, payload, ← mapCells_iff, mapped, count, Bind.bind,
            Except.bind]
          rintro rfl
          exact count
    · simp [readColumn, ColumnWire, bitmap, payload, Bind.bind, Except.bind]
  · simp [readColumn, ColumnWire, bitmap, Bind.bind, Except.bind]

theorem readColumns_iff (body : KBytes) (fields : List Field) (nodes : List FieldNode)
    (descriptors : List Buffer) (columns : List Column) :
    readColumns body fields nodes descriptors = .ok columns ↔
      ColumnsWire body fields nodes descriptors columns := by
  induction fields generalizing nodes descriptors columns with
  | nil => cases nodes <;> cases descriptors <;> cases columns <;> simp [readColumns, ColumnsWire]
  | cons field fields ih =>
    cases nodes with
    | nil => cases columns <;> simp [readColumns, ColumnsWire]
    | cons node nodes =>
      cases next : nextColumn body field.type descriptors with
      | none => cases columns <;> simp [readColumns, ColumnsWire, next]
      | some part =>
        obtain ⟨buffers, rest⟩ := part
        cases column : readColumn node buffers <;>
          cases tail : readColumns body fields nodes rest <;>
          cases columns <;> simp [readColumns, ColumnsWire, next, column, tail, ← readColumn_iff,
            ← ih, Bind.bind, Except.bind, pure, Except.pure, and_assoc]

theorem decodeBatch_iff (limits : ObservationLimits) {fields : List Field}
    (frame : BatchFrame fields) (rows : List Row) :
    decodeBatch limits frame = .ok rows ↔ Body.checkBatch limits frame = .ok () ∧ BatchWire frame rows := by
  cases budget : Body.checkBatch limits frame with
  | error reason => simp [decodeBatch, budget, Bind.bind, Except.bind]
  | ok result =>
    cases result
    cases columns : Body.readColumns frame.body fields frame.metadata.nodes frame.metadata.buffers <;>
      simp [decodeBatch, BatchWire, budget, ← readColumns_iff, columns, Bind.bind, Except.bind,
        pure, Except.pure, eq_comm]

private theorem cellsLength {buffers : ColumnBuffers} {indices : List Nat} {values : Column}
    (wire : CellsWire buffers indices values) : values.length = indices.length := by
  induction indices generalizing values with
  | nil => cases values <;> simp_all [CellsWire]
  | cons index indices ih =>
    cases values with
    | nil => exact wire.elim
    | cons value values => exact congrArg Nat.succ (ih wire.2)

private theorem columnsShape (body : KBytes) (rowCount : Nat)
    {fields : List Field} {nodes : List FieldNode} {descriptors : List Buffer} {columns : List Column}
    (wire : ColumnsWire body fields nodes descriptors columns)
    (aligned : ∀ pair ∈ fields.zip nodes, pair.2.length = rowCount) :
    columns.length = fields.length ∧ ∀ column ∈ columns, column.length = rowCount := by
  induction fields generalizing nodes descriptors columns with
  | nil =>
    cases nodes <;> cases descriptors <;> cases columns <;>
      simp_all [ColumnsWire]
  | cons field fields ih =>
    cases nodes with
    | nil => cases columns <;> exact wire.elim
    | cons node nodes =>
      cases columns with
      | nil => exact wire.elim
      | cons column columns =>
        obtain ⟨buffers, rest, _, columnWire, tailWire⟩ := wire
        have headLength : node.length = rowCount := aligned (field, node) (by simp)
        have tailAligned (pair : Field × FieldNode) (member : pair ∈ fields.zip nodes) :
            pair.2.length = rowCount := aligned pair (by simp [member])
        obtain ⟨count, lengths⟩ := ih tailWire tailAligned
        refine ⟨congrArg Nat.succ count, ?_⟩
        intro chosen member
        rcases List.mem_cons.mp member with rfl | inTail
        · simpa [headLength] using cellsLength columnWire.2.2.1
        · exact lengths chosen inTail

private theorem rowsOfColumns_shape (count : Nat) (columns : List Column)
    (aligned : ∀ column ∈ columns, column.length = count) :
    (rowsOfColumns count columns).length = count ∧
      ∀ row ∈ rowsOfColumns count columns, row.length = columns.length := by
  induction columns with
  | nil => simp [rowsOfColumns]
  | cons column columns ih =>
    obtain ⟨tailCount, tailShape⟩ := ih (fun c hc => aligned c (List.mem_cons_of_mem _ hc))
    have headCount := aligned column (by simp)
    change (List.zipWith List.cons column (rowsOfColumns count columns)).length = count ∧ _
    refine ⟨by simp [headCount, tailCount], ?_⟩
    intro row member
    change row ∈ List.zipWith List.cons column (rowsOfColumns count columns) at member
    obtain ⟨index, bound, rfl⟩ := List.mem_iff_getElem.mp member
    rw [List.getElem_zipWith]
    exact congrArg Nat.succ (tailShape _ (List.getElem_mem _))

theorem BatchWire.shape {fields : List Field} {frame : BatchFrame fields} {rows : List Row}
    (wire : BatchWire frame rows) :
    rows.length = frame.metadata.rowCount ∧ ∀ row ∈ rows, row.length = fields.length := by
  obtain ⟨columns, columnWire, rfl⟩ := wire
  obtain ⟨count, aligned⟩ := columnsShape frame.body frame.metadata.rowCount columnWire
    (fun pair member => (frame.layout.2.2.1 pair member).1)
  rw [← count]
  exact rowsOfColumns_shape frame.metadata.rowCount columns aligned

end Silmaril.Proofs.Formats.Arrow
