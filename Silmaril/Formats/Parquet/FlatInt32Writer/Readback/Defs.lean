module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs

/-! Field projection for the flat INT32 scan of one written column. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer

def Column.scanField (column : Column) : FlatScan.Field :=
  ⟨column.name, match column.values with | .required _ => .required | .optional _ => .optional⟩

/-- Use the writer's header and page limits, and the exact input dimensions. -/
def Limits.scanLimits (limits : Limits) (input : Input) : FlatScan.Limits :=
  ⟨limits.footer, limits.pageReader, input.rowCount, input.columns.length,
    input.rowCount * input.columns.length, limits.page.scalar.compressedBytes⟩

def Column.scanObservation (column : Column) : FlatScan.Field × List (Option Int32) :=
  (column.scanField, column.values.slots)

/-- Row order is the common slot order of the columns, in declared column order. -/
def rowsFromSlots (count : Nat) (columns : List (List (Option Int32))) : List (List (Option Int32)) :=
  (columns.foldl (List.zipWith fun row cell => cell :: row) (List.replicate count [])).map List.reverse

def Input.rows (input : Input) : List (List (Option Int32)) :=
  rowsFromSlots input.rowCount (input.columns.map (·.values.slots))

end Silmaril.Formats.Parquet.FlatInt32Writer
