module

public import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs
import all Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs
import Silmaril.Formats.ThriftCompact.Traversal.List.Thms
import Silmaril.Formats.ThriftCompact.Traversal.Thms
import Init.Data.List.Lemmas

namespace Silmaril.Proofs.Formats.Parquet.Footer.ColumnOrder

open Silmaril.Formats.Parquet
open Silmaril.Formats.ThriftCompact
open Silmaril.Formats.Parquet.Footer.ColumnOrder
open Silmaril.Formats.ThriftCompact.Traversal (Reader Field)

@[local simp] private theorem except_throw {ε α : Type} (reason : ε) :
    (throw reason : Except ε α) = .error reason := rfl

@[local simp] private theorem except_throwThe {ε α : Type} (reason : ε) :
    (throwThe ε reason : Except ε α) = .error reason := rfl

public theorem readStructList_erase {ε : Type} (reader : Reader) (field : Field)
    (fail : Footer.ColumnOrder.Error → ε) :
    ((readStructList reader field).map (List.map Item.fields)).mapError fail = (do
      if field.type ≠ .payload .list then throw (fail (.fieldType field.id))
      let (items, next) ← Traversal.readList reader (fail ∘ Footer.ColumnOrder.Error.compact) .struct
        (fun offset => (Traversal.readStruct reader offset).mapError (fail ∘ Footer.ColumnOrder.Error.compact))
        field.start
      if next ≠ field.stop then throw (fail (.fieldExtent field.id))
      pure items) := by
  have callback : (fun offset => (Traversal.readStruct reader offset).mapError
        (fail ∘ Footer.ColumnOrder.Error.compact)) =
      (fun offset => Traversal.mapReadResult Item.fields fail (readItem reader offset)) := by
    funext offset
    cases parsed : Traversal.readStruct reader offset <;>
      simp [readItem, Traversal.mapReadResult, parsed, Except.map, Except.mapError]
  rw [callback, Traversal.readList_map]
  by_cases type : field.type = .payload .list
  · cases parsed : Traversal.readList reader Footer.ColumnOrder.Error.compact .struct (readItem reader) field.start with
    | error reason =>
      simp [readStructList, type, parsed, Traversal.mapReadResult, Except.map, Except.mapError, bind, Except.bind]
    | ok pair =>
      obtain ⟨items, next⟩ := pair
      by_cases extent : next = field.stop <;>
        simp [readStructList, type, parsed, extent, Traversal.mapReadResult, Except.map, Except.mapError,
          bind, Except.bind, pure, Except.pure, throw]
  · simp [readStructList, type, Except.map, Except.mapError, bind, Except.bind, throw]

private theorem structList_sound {reader : Reader} {field : Field} {items : List Item}
    (h : readStructList reader field = .ok items) : StructListWire reader field items := by
  by_cases type : field.type = .payload .list
  · cases parsed : Traversal.readList reader Footer.ColumnOrder.Error.compact .struct (readItem reader) field.start with
    | error reason => simp [readStructList, type, parsed, bind, Except.bind] at h
    | ok pair =>
      obtain ⟨found, next⟩ := pair
      by_cases extent : next = field.stop
      · simp [readStructList, type, parsed, extent, bind, Except.bind, pure, Except.pure] at h
        subst items
        subst next
        exact ⟨type, Traversal.readList_trace parsed⟩
      · simp [readStructList, type, parsed, extent, bind, Except.bind, throw] at h
  · simp [readStructList, type, bind, Except.bind] at h

private theorem field?_some {fields : List Field} {id : Int} {field : Field}
    (h : field? fields id = .ok (some field)) : fields.filter (·.id == id) = [field] := by
  unfold field? at h
  split at h <;> simp_all

private theorem field?_none {fields : List Field} {id : Int}
    (h : field? fields id = .ok none) : fields.filter (·.id == id) = [] := by
  unfold field? at h
  split at h <;> simp_all

public theorem readSelection_wire {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {result : Selection}
    (h : readSelection limits snapshot column = .ok result) :
    SelectionWire limits snapshot column result := by
  unfold readSelection at h
  by_cases cap : snapshot.footer.stop - snapshot.footer.start > limits.maxFooterBytes
  · simp [cap, bind, Except.bind] at h
  simp only [cap, ite_false] at h
  cases root : Traversal.readStruct (footerReader limits snapshot) 0 with
  | error reason => simp [root, Except.mapError, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨fields, next⟩ := pair
    simp only [root, Except.mapError, bind, Except.bind] at h
    by_cases extent : next = (footerReader limits snapshot).source.length
    · simp only [extent, ne_self_iff_false, ite_false] at h
      have exactRoot : Traversal.readStruct (footerReader limits snapshot) 0 = .ok (fields, (footerReader limits snapshot).source.length) := by
        simpa [extent] using root
      cases schemaFound : field? fields 2 with
      | error reason => simp [schemaFound] at h
      | ok optional =>
        cases optional with
        | none => simp [schemaFound, throw] at h
        | some schemaField =>
          simp only [schemaFound] at h
          cases schemaParsed : readStructList (footerReader limits snapshot) schemaField with
          | error reason => simp [schemaParsed] at h
          | ok schema =>
            rw [schemaParsed] at h
            by_cases count : schema.length = snapshot.metadata.schema.length
            · simp only [← count, ne_self_iff_false, ite_false] at h
              cases leafAt : schema[column + 1]? with
              | none => simp [leafAt, throw] at h
              | some leaf =>
                simp only [leafAt] at h
                cases orderFound : field? fields 7 with
                | error reason => simp [orderFound] at h
                | ok optional =>
                  cases optional with
                  | none =>
                    simp [orderFound, pure, Except.pure] at h
                    subst result
                    exact ⟨Nat.le_of_not_gt cap, rfl, fields, schema, exactRoot,
                      field?_some schemaFound, structList_sound schemaParsed, count, leafAt,
                      field?_none orderFound⟩
                  | some orderField =>
                    simp only [orderFound] at h
                    cases ordersParsed : readStructList (footerReader limits snapshot) orderField with
                    | error reason => simp [ordersParsed] at h
                    | ok orders =>
                      rw [ordersParsed] at h
                      by_cases orderCount : orders.length + 1 = schema.length
                      · simp only [orderCount, ne_self_iff_false, ite_false] at h
                        cases orderAt : orders[column]? with
                        | none => simp [orderAt, throw] at h
                        | some order =>
                          simp [orderAt, pure, Except.pure] at h
                          subst result
                          exact ⟨Nat.le_of_not_gt cap, rfl, fields, schema, exactRoot,
                            field?_some schemaFound, structList_sound schemaParsed, count, leafAt,
                            orders, field?_some orderFound, structList_sound ordersParsed, orderCount, orderAt⟩
                      · simp [orderCount, throw] at h
            · simp [count, throw] at h
    · simp [extent, throw] at h

private theorem structList_item {reader : Reader} {field : Field} {items : List Item} {item : Item}
    (wire : StructListWire reader field items) (member : item ∈ items) :
    Traversal.readStruct reader item.start = .ok (item.fields, item.stop) := by
  obtain ⟨_, _, _, _, _, _, trace⟩ := wire
  obtain ⟨start, next, parsed⟩ := Traversal.ListTrace.mem_read trace member
  cases found : Traversal.readStruct reader start with
  | error reason => simp [readItem, found, Except.map, Except.mapError] at parsed
  | ok pair =>
    obtain ⟨fields, stop⟩ := pair
    simp [readItem, found, Except.map, Except.mapError] at parsed
    obtain ⟨rfl, rfl⟩ := parsed
    exact found

private theorem selectedLeaf_struct {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {result : Selection} (wire : SelectionWire limits snapshot column result) :
    Traversal.readStruct result.reader result.leaf.item.start =
      .ok (result.leaf.item.fields, result.leaf.item.stop) := by
  obtain ⟨_, _, _, _, items, _, atOrdinal, _⟩ := wire.fields
  exact structList_item items (List.mem_of_getElem? atOrdinal)

private theorem selectedOrder_struct {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {result : Selection} (wire : SelectionWire limits snapshot column result)
    {slot : Slot} (selected : result.order = some slot) :
    Traversal.readStruct result.reader slot.item.start = .ok (slot.item.fields, slot.item.stop) := by
  obtain ⟨_, _, _, _, _, _, _, order⟩ := wire.fields
  rw [selected] at order
  obtain ⟨_, _, items, _, atOrdinal⟩ := order
  exact structList_item items (List.mem_of_getElem? atOrdinal)

public theorem readMarker_sound {reader : Reader} {item : Item} {marker : Marker}
    (h : readMarker reader item = .ok marker) : MarkerWire reader item marker := by
  cases selected : item.fields with
  | nil => simp [readMarker, selected, throw] at h
  | cons member rest =>
    cases rest with
    | cons => simp [readMarker, selected, throw] at h
    | nil =>
      by_cases type : member.type = .payload .struct
      · cases parsed : Traversal.readStruct reader member.start with
        | error reason =>
          simp [readMarker, selected, type, parsed, Except.mapError, bind, Except.bind] at h
        | ok pair =>
          obtain ⟨fields, stop⟩ := pair
          by_cases extent : stop = member.stop
          · by_cases invalid : (member.id = 1 ∨ member.id = 2 ∨ member.id = 3) ∧ fields ≠ []
            · simp [readMarker, selected, type, parsed, extent, invalid, Except.mapError, bind, Except.bind, throw] at h
            · simp [readMarker, selected, type, parsed, extent, invalid, Except.mapError, bind, Except.bind,
                pure, Except.pure] at h
              subst marker
              refine ⟨member, fields, selected, rfl, type, by simpa [extent] using parsed, ?_⟩
              intro known
              simpa [known] using invalid
          · simp [readMarker, selected, type, parsed, extent, Except.mapError, bind, Except.bind, throw] at h
      · simp [readMarker, selected, type, bind, Except.bind] at h

public theorem readFlat_wire {limits : Footer.Limits} {snapshot : Snapshot.Checked}
    {column : Nat} {result : FlatLeaf} (h : readFlat limits snapshot column = .ok result) :
    FlatWire limits snapshot column result := by
  cases schema : snapshot.metadata.schema with
  | nil => simp [readFlat, schema, throw] at h
  | cons root leaves =>
    by_cases flat : isFlat root leaves = true
    · cases ordinal : leaves[column]? with
      | none => simp [readFlat, schema, flat, ordinal, throw] at h
      | some leaf =>
        cases selection : readSelection limits snapshot column with
        | error reason => simp [readFlat, schema, flat, ordinal, selection, bind, Except.bind] at h
        | ok selected =>
          by_cases leafWithin : selected.leaf.within selected.reader
          · have wire := readSelection_wire selection
            have leafAt : snapshot.metadata.schema[column + 1]? = some leaf := by
              simpa [schema] using ordinal
            have shape : ∃ root leaves, snapshot.metadata.schema = root :: leaves ∧ isFlat root leaves = true :=
              ⟨root, leaves, schema, flat⟩
            cases order : selected.order with
            | none =>
              simp [readFlat, schema, flat, ordinal, selection, leafWithin, order, pure, Except.pure,
                bind, Except.bind] at h
              subst result
              exact ⟨wire, shape, leafAt, leafWithin, selectedLeaf_struct wire, by simp [order]⟩
            | some slot =>
              by_cases orderWithin : slot.within selected.reader
              · cases decoded : readMarker selected.reader slot.item with
                | error reason =>
                  simp [readFlat, schema, flat, ordinal, selection, leafWithin, order, orderWithin,
                    decoded, Option.mapM, bind, Except.bind] at h
                | ok marker =>
                  simp [readFlat, schema, flat, ordinal, selection, leafWithin, order, orderWithin,
                    decoded, Option.mapM, pure, Except.pure, bind, Except.bind] at h
                  subst result
                  refine ⟨wire, shape, leafAt, leafWithin, selectedLeaf_struct wire, ?_⟩
                  rw [order]
                  exact ⟨orderWithin, selectedOrder_struct wire order, readMarker_sound decoded⟩
              · simp [readFlat, schema, flat, ordinal, selection, leafWithin, order, orderWithin,
                  Option.mapM, bind, Except.bind, throw] at h
          · simp [readFlat, schema, flat, ordinal, selection, leafWithin, bind, Except.bind, throw] at h
    · simp [readFlat, schema, flat, bind, Except.bind] at h

end Silmaril.Proofs.Formats.Parquet.Footer.ColumnOrder
