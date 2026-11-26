module

public import Silmaril.Data.TimeSeries.Defs
public import Silmaril.Semantics.Relational.Table.Defs

/-! Projections of the public relational row and column models.
List positions supply the observation order. For a table keyed by row IDs,
use `Silmaril.Relational.orderRows` with `Series.ofRows`. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Series

variable {Index Kind : Type*} {kind : Index → Kind} {Cell : Kind → Type*}

/-- Select timestamp and value columns from a typed relational table. -/
def ofTable (table : Relational.Table kind Cell) (time value : Index) :
    Series table.length (Cell (kind time)) (Cell (kind value)) :=
  ofRows (fun row => row time) (fun row => row value) table.get

/-- Select two aligned columns, using their common row count as the series length. -/
def ofAlignedColumns (columns : Relational.AlignedColumns kind Cell) (time value : Index) :
    Series columns.rowCount (Cell (kind time)) (Cell (kind value)) :=
  ⟨fun i => ⟨(columns.values time).get (i.cast (columns.length_eq time).symm),
    (columns.values value).get (i.cast (columns.length_eq value).symm)⟩⟩

end Silmaril.Data.TimeSeries.Series
