module

public import Silmaril.Formats.Parquet.ColumnIndex.Signed.Compatibility.Defs
import Silmaril.Proofs.Formats.Parquet.ColumnIndex.Signed.Compatibility

/-! Equivalence to the signed diagnostic before sharing the footer selector. -/

public section

namespace Silmaril.Formats.Parquet.ColumnIndex.Signed

theorem readOrderFields_eq_reference (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) :
    readOrderFields limits snapshot binding = Compatibility.readOrderFields limits snapshot binding :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.Compatibility.readOrderFields_eq_reference limits snapshot binding

/-- The shared selector preserves the whole gate result, including typed errors. -/
theorem checkOrder_eq_reference (limits : Footer.Limits) (snapshot : Snapshot.Checked)
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) :
    checkOrder limits snapshot binding = Compatibility.checkOrder limits snapshot binding :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.Compatibility.checkOrder_eq_reference limits snapshot binding

/-- The post-read diagnostic has the same value and error precedence as before. -/
theorem diagnose_eq_reference (limits : Limits) {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) (slots : Slots) :
    diagnose limits binding group slots = Compatibility.diagnose limits binding group slots :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.Compatibility.diagnose_eq_reference limits binding group slots

theorem read_eq_reference (limits : Limits) {snapshot : Snapshot.Checked}
    {name : String} {layout : FlatColumn.Layout}
    (binding : FlatColumn.Binding snapshot ⟨name, .int32, layout⟩) (group : Nat) :
    read limits binding group = (readFull limits binding group).map
      (fun slots => ⟨slots, Compatibility.diagnose limits binding group slots⟩) :=
  Proofs.Formats.Parquet.ColumnIndex.Signed.Compatibility.read_eq_reference limits binding group

end Silmaril.Formats.Parquet.ColumnIndex.Signed
