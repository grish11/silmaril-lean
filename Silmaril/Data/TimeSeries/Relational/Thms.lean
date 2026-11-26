module

public import Silmaril.Data.TimeSeries.Relational.Defs

/-! Row and aligned-column projections agree at each position. -/

@[expose] public section

namespace Silmaril.Data.TimeSeries.Series

variable {Index Kind : Type*} {kind : Index → Kind} {Cell : Kind → Type*}

/-- Changing the table's storage orientation preserves both projected columns and their order. -/
@[simp] theorem ofAlignedColumns_ofRows (table : Relational.Table kind Cell) (time value : Index) :
    ofAlignedColumns (Relational.AlignedColumns.ofRows table) time value = ofTable table time value := by
  apply congrArg Series.mk
  funext i
  simp [Relational.AlignedColumns.ofRows, List.get_eq_getElem, Fin.cast]
  exact ⟨rfl, rfl⟩

end Silmaril.Data.TimeSeries.Series
