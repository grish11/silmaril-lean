module

public import Silmaril.Formats.Parquet.Footer.NestedLeaf.Defs
import all Silmaril.Formats.Parquet.Footer.NestedLeaf.Defs
import Silmaril.Formats.Parquet.Footer.ColumnOrder.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.Footer.NestedLeaf

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Footer.NestedLeaf
open Silmaril.Formats.ThriftCompact
open Silmaril.Formats.ThriftCompact.Traversal (Field)

public theorem checkShape_ok_iff {schema : List Footer.SchemaElement} {shape : Shape} :
    checkShape schema = .ok shape ↔
      schema = [shape.root, shape.parent, shape.first, shape.second] ∧ shape.admitted := by
  constructor
  · intro success
    unfold checkShape at success
    split at success
    · dsimp only at success
      split at success
      · obtain rfl := Except.ok.inj success
        exact ⟨rfl, by assumption⟩
      · cases success
    · cases success
  · rintro ⟨rfl, admitted⟩
    cases shape
    simp [checkShape, admitted]

public theorem readItems_wire {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {container : Field} {items : List Footer.ColumnOrder.Item}
    (h : readItems limits snapshot = .ok (container, items)) :
    ItemsWire limits snapshot container items := by
  unfold readItems at h
  by_cases cap : snapshot.footer.stop - snapshot.footer.start > limits.maxFooterBytes
  · simp [cap, throw] at h
  simp only [cap, ite_false] at h
  set reader := Footer.ColumnOrder.footerReader limits snapshot
  cases parsed : Traversal.readStruct reader 0 with
  | error reason => simp [parsed, Except.mapError, bind, Except.bind] at h
  | ok result =>
    obtain ⟨fields, next⟩ := result
    simp only [parsed, Except.mapError, bind, Except.bind] at h
    by_cases extent : next = reader.source.length
    · simp only [extent, ne_self_iff_false, ite_false] at h
      cases found : Footer.ColumnOrder.field? fields 2 with
      | error reason => simp [found] at h
      | ok optional =>
        cases optional with
        | none => simp [found, throw] at h
        | some field =>
          cases schema : Footer.ColumnOrder.readStructList reader field with
          | error reason => simp [found, schema] at h
          | ok values =>
            simp [found, schema, pure, Except.pure] at h
            obtain ⟨rfl, rfl⟩ := h
            have unique : fields.filter (·.id == 2) = [field] := by
              unfold Footer.ColumnOrder.field? at found
              split at found <;> simp_all
            exact ⟨Nat.le_of_not_gt cap, fields, extent ▸ parsed, unique,
              Footer.ColumnOrder.readStructList_wire schema⟩
    · simp [extent, throw] at h

public theorem select_wire {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {selection : Selection snapshot}
    (h : select limits snapshot column = .ok selection) : Wire limits column selection := by
  unfold select at h
  by_cases bound : 2 ≤ column
  · simp [bound, throw] at h
  simp only [bound, ite_false] at h
  cases topology : checkShape snapshot.metadata.schema with
  | error reason => simp [topology, bind, Except.bind] at h
  | ok shape =>
    simp only [topology, bind, Except.bind] at h
    cases type : (if column = 0 then shape.first else shape.second).physicalType with
    | none => simp [type, throw] at h
    | some physical =>
      rw [type] at h
      cases raw : readItems limits snapshot with
      | error reason => simp [raw] at h
      | ok pair =>
        obtain ⟨container, items⟩ := pair
        rw [raw] at h
        dsimp only at h
        split at h
        · rename_i itemsMatch rootItem parentItem first second
          by_cases annotated : parentItem.fields.any (fun field => field.id == 6 || field.id == 10) = true
          · simp [annotated, throw] at h
          have absent : ∀ field ∈ parentItem.fields, field.id ≠ 6 ∧ field.id ≠ 10 := by
            intro field member
            constructor <;> intro id <;>
              exact annotated (List.any_eq_true.mpr ⟨field, member, by simp [id]⟩)
          simp only [annotated, Bool.false_eq_true, ite_false] at h
          by_cases within : Footer.ColumnOrder.Slot.within (Footer.ColumnOrder.footerReader limits snapshot)
                ⟨container, parentItem⟩ ∧ Footer.ColumnOrder.Slot.within (Footer.ColumnOrder.footerReader limits snapshot)
                ⟨container, if column = 0 then first else second⟩
          · rw [ite_eq_right (not_not.mpr within)] at h
            have whole := readItems_wire raw
            obtain ⟨schema, admitted⟩ := checkShape_ok_iff.mp topology
            obtain rfl := Except.ok.inj h
            refine ⟨rfl, Nat.lt_of_not_ge bound, ⟨shape, admitted, schema⟩, ?_, ?_, type,
              absent, within.1, within.2, _, whole, ?_, ?_, ?_⟩
            · simp [schema]
            · have side : column = 0 ∨ column = 1 := by omega
              rcases side with rfl | rfl <;> simp [Selection.schemaOrdinal, schema]
            · rfl
            · rfl
            · have side : column = 0 ∨ column = 1 := by omega
              rcases side with rfl | rfl <;> simp [Selection.schemaOrdinal]
          · rw [ite_eq_left within] at h
            cases h
        · cases h

public theorem selectChunk_wire {snapshot : Snapshot.Checked} {selection : Selection snapshot}
    {ordinal : Nat} {group : Footer.RowGroup} {chunk : Footer.ColumnChunk}
    (h : selectChunk selection ordinal = .ok (group, chunk)) :
    snapshot.groupAt ordinal = some group ∧ group.columns[selection.columnOrdinal]? = some chunk ∧
      chunk.metadata.pathInSchema = selection.path ∧ chunk.metadata.physicalType = selection.physical := by
  unfold selectChunk at h
  split at h
  · rename_i actualGroup groupAt
    split at h
    · rename_i actualChunk chunkAt
      split at h
      · cases h
      rename_i matched
      obtain ⟨rfl, rfl⟩ := Except.ok.inj h
      exact ⟨groupAt, chunkAt, not_not.mp matched⟩
    · cases h
  · cases h

end Silmaril.Proofs.Formats.Parquet.Footer.NestedLeaf
