module

public import Silmaril.Formats.Parquet.Date.Events.ToIpc.Defs

/-! # Explicit page-less DATE rows under a pinned PyArrow profile -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.PageLess

open Silmaril.Relational

abbrev OpenError := Footer.PageLessInt32.Error ⊕ Date.Error

/-- The exact original ordinal is used for both paths. The framed path
retains the existing DATE scanner, including its default CRC policy. -/
def readGroup (checked : Date.Checked) (limits : Date.Limits) (index : Nat) :
    Except Date.Error Date.RowGroup := do
  let some group := checked.snapshot.groupAt index | throw (.groupIndex index)
  if Footer.PageLessInt32.isPageLess group then
    Date.checkColumn checked.binding group
    let _ ← (FlatScan.flatSchema limits.scan checked.snapshot.metadata.schema).mapError Date.Error.scan
    return ⟨checked.binding, 0, ⟨#[], rfl⟩⟩
  else checked.readGroup limits index

def rowsAt (checked : Date.Checked) (limits : Date.Limits) (index : Nat) :
    Except Date.Events.Error (Reader.RowGroup (Date.Events.schema checked) Date.Events.Cell) :=
  ((readGroup checked limits index).map (Date.Events.rows checked)).mapError (.groupFailure index)

abbrev Observed := Σ schema : Scan.Schema String Date.Events.Kind, Arrow.Events.Trace schema Date.Events.Cell Date.Events.Error

/-- Enumerate every original group, including those that occupy zero bytes. -/
def trace (checked : Date.Checked) (limits : Date.Limits) :
    Arrow.Events.Trace (Date.Events.schema checked) Date.Events.Cell Date.Events.Error :=
  let groups := Reader.denoteGroups (rowsAt checked limits) (List.range checked.snapshot.groupCount)
  ⟨groups.1.map AlignedColumns.ofRows, groups.2⟩

def readAll (limits : Date.Limits) (input : Bytes) : Except OpenError Observed := do
  let checked ← Date.openCheckedPageLess limits input
  return ⟨Date.Events.schema checked, trace checked limits⟩

/-- The checked native writer receives exactly one batch per group after EOF. -/
def toIpc (source : Date.Limits) (output : Arrow.ObservationLimits) (input : Bytes) :
    Except (OpenError ⊕ Date.Events.ToIpc.Error) KBytes := do
  let observed ← (readAll source input).mapError Sum.inl
  (Date.Events.ToIpc.emit output (.ok observed)).mapError Sum.inr

end Silmaril.Formats.Parquet.Date.PageLess
