module

public import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs
public import Silmaril.Formats.Parquet.Snapshot.FlatInt32.Defs

/-! The physical open schema and the matching read limits for emitted files. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer

open Silmaril.Relational

/-- The snapshot opens with all physical column names in declared wire order. -/
def Input.arrowSchema (input : Input) : Scan.Schema String Unit :=
  ⟨input.columns.length, fun index => (input.columns[index.val].name, ())⟩

/-- Use the same checked footer and page budgets as the writer and bound the
scan by the input dimensions. The footer is validated at the writer's depth. -/
def Limits.snapshotLimits (limits : Limits) (input : Input) : Snapshot.FlatInt32.Limits :=
  ⟨⟨limits.footer, 2⟩, limits.scanLimits input, limits.page.scalar⟩

end Silmaril.Formats.Parquet.FlatInt32Writer
