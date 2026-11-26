module

public import Silmaril.Formats.Parquet.Footer.Validation.Defs
import Silmaril.Proofs.Formats.Parquet.Footer.Validation

public section

namespace Silmaril.Formats.Parquet.Footer

/-- Checked footer counts agree in natural arithmetic since every group
count is nonnegative. -/
theorem validate_rowCounts {start depth : Nat} {metadata : Metadata}
    (success : validate start depth metadata = .ok ()) :
    metadata.numRows.toNat = (metadata.rowGroups.map (·.numRows.toNat)).sum :=
  Proofs.Formats.Parquet.Footer.validate_rowCounts success

end Silmaril.Formats.Parquet.Footer
