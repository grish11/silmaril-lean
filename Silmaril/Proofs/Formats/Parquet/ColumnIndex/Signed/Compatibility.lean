module

public import Silmaril.Formats.Parquet.ColumnIndex.Signed.Compatibility.Defs
import all Silmaril.Formats.Parquet.ColumnIndex.Signed.Compatibility.Defs
import all Silmaril.Formats.Parquet.ColumnIndex.Signed.Defs
import Silmaril.Formats.Parquet.Footer.ColumnOrder.Thms

namespace Silmaril.Proofs.Formats.Parquet.ColumnIndex.Signed.Compatibility

open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.ColumnIndex.Signed
open Silmaril.Formats.ThriftCompact
open Silmaril.Formats.ThriftCompact.Traversal (Field Reader)

@[local simp] private theorem except_throw {ε α : Type} (reason : ε) :
    (throw reason : Except ε α) = .error reason := rfl

@[local simp] private theorem except_throwThe {ε α : Type} (reason : ε) :
    (throwThe ε reason : Except ε α) = .error reason := rfl

private theorem field_eq (fields : List Field) (id : Int) :
    ((Footer.ColumnOrder.field? fields id).mapError OrderError.ofColumnOrder) =
      ColumnIndex.Signed.Compatibility.field? fields id := by
  cases found : fields.filter (·.id == id) with
  | nil => simp [Footer.ColumnOrder.field?, ColumnIndex.Signed.Compatibility.field?, found, Except.mapError]
  | cons field rest =>
    cases rest <;> simp [Footer.ColumnOrder.field?, ColumnIndex.Signed.Compatibility.field?, found,
      Except.mapError, OrderError.ofColumnOrder]

private theorem list_eq (reader : Reader) (field : Field) :
    ((Footer.ColumnOrder.readStructList reader field).map
      (List.map Footer.ColumnOrder.Item.fields)).mapError OrderError.ofColumnOrder =
      ColumnIndex.Signed.Compatibility.structList reader field := by
  have callback : ColumnIndex.Signed.Compatibility.readStruct reader =
      (fun offset => (Traversal.readStruct reader offset).mapError OrderError.compact) := rfl
  simpa only [ColumnIndex.Signed.Compatibility.structList, callback, Function.comp_def,
    OrderError.ofColumnOrder] using Footer.ColumnOrder.readStructList_erase reader field OrderError.ofColumnOrder

public theorem readOrderFields_eq_reference (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) :
    ColumnIndex.Signed.readOrderFields limits snapshot binding =
      ColumnIndex.Signed.Compatibility.readOrderFields limits snapshot binding := by
  unfold ColumnIndex.Signed.readOrderFields ColumnIndex.Signed.Compatibility.readOrderFields
    Footer.ColumnOrder.readSelection
  dsimp only [Footer.ColumnOrder.footerReader, FlatColumn.Binding.leafOrdinal,
    ColumnIndex.Signed.Compatibility.readStruct]
  set reader : Reader := ⟨Footer.fileBytes snapshot.bytes snapshot.footer.start snapshot.footer.stop,
    limits.compact, limits.varintMode⟩
  by_cases cap : snapshot.footer.stop - snapshot.footer.start > limits.maxFooterBytes
  · simp [cap, Except.mapError, OrderError.ofColumnOrder, bind, Except.bind, throw]
  cases root : Traversal.readStruct reader 0 with
  | error reason => simp [cap, Except.mapError, OrderError.ofColumnOrder, bind, Except.bind]
  | ok pair =>
    obtain ⟨fields, next⟩ := pair
    by_cases extent : next = (Footer.fileBytes snapshot.bytes snapshot.footer.start snapshot.footer.stop).length
    · simp only [cap, ite_false, Except.mapError, bind, Except.bind,
        extent]
      rw [← field_eq]
      cases sf : Footer.ColumnOrder.field? fields 2 with
      | error reason => simp [Except.mapError]
      | ok optional =>
        cases optional with
        | none => simp [Except.mapError, throw, OrderError.ofColumnOrder]
        | some schemaField =>
          simp only [Except.mapError]
          rw [← list_eq]
          cases schema : Footer.ColumnOrder.readStructList reader schemaField with
          | error reason => simp [Except.map, Except.mapError]
          | ok nodes =>
            simp only [Except.map, Except.mapError, List.length_map]
            by_cases rightCount : nodes.length = snapshot.metadata.schema.length
            · simp only [← rightCount, ne_self_iff_false, ite_false, List.getElem?_map]
              cases leaf : nodes[binding.columnOrdinal + 1]? with
              | none => simp [OrderError.ofColumnOrder, throw]
              | some item =>
                simp only [Option.map_some]
                rw [← field_eq]
                cases ofield : Footer.ColumnOrder.field? fields 7 with
                | error reason => simp [Except.mapError]
                | ok optional =>
                  cases optional with
                  | none => simp [Except.mapError, pure, Except.pure, throw]
                  | some orderField =>
                    simp only [Except.mapError]
                    rw [← list_eq]
                    cases orders : Footer.ColumnOrder.readStructList reader orderField with
                    | error reason => simp [Except.map, Except.mapError]
                    | ok entries =>
                      simp only [Except.map, Except.mapError, List.length_map,
                        List.getElem?_map]
                      by_cases orderCount : entries.length + 1 = nodes.length
                      · cases selected : entries[binding.columnOrdinal]? <;>
                          simp [orderCount, OrderError.ofColumnOrder, throw, pure, Except.pure]
                      · simp [orderCount, OrderError.ofColumnOrder, throw]
            · simp [rightCount, OrderError.ofColumnOrder, throw]
    · simp [cap, extent, OrderError.ofColumnOrder, Except.mapError, bind, Except.bind, throw]

public theorem checkOrder_eq_reference (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) :
    ColumnIndex.Signed.checkOrder limits snapshot binding =
      ColumnIndex.Signed.Compatibility.checkOrder limits snapshot binding := by
  simp only [ColumnIndex.Signed.checkOrder, ColumnIndex.Signed.Compatibility.checkOrder,
    readOrderFields_eq_reference]

public theorem diagnose_eq_reference (limits : Limits) {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) (slots : Slots) :
    ColumnIndex.Signed.diagnose limits binding group slots =
      ColumnIndex.Signed.Compatibility.diagnose limits binding group slots := by
  simp only [ColumnIndex.Signed.diagnose, ColumnIndex.Signed.Compatibility.diagnose,
    checkOrder_eq_reference]
  rfl

public theorem read_eq_reference (limits : Limits) {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) :
    ColumnIndex.Signed.read limits binding group =
      (readFull limits binding group).map
        (fun slots => ⟨slots, ColumnIndex.Signed.Compatibility.diagnose limits binding group slots⟩) := by
  unfold ColumnIndex.Signed.read
  simp only [diagnose_eq_reference]

end Silmaril.Proofs.Formats.Parquet.ColumnIndex.Signed.Compatibility
