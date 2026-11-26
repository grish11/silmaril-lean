module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
public import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs

/-! Field projection for the flat INT32 scan of one written column. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer

def Column.scanField (column : Column) : FlatScan.Field :=
  ⟨column.name, match column.values with | .required _ => .required | .optional _ => .optional⟩

end Silmaril.Formats.Parquet.FlatInt32Writer
