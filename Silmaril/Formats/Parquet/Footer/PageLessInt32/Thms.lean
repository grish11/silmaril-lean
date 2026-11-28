module

public import Silmaril.Formats.Parquet.Footer.PageLessInt32.Defs
import Silmaril.Proofs.Formats.Parquet.Footer.PageLessInt32.Validation

public section

namespace Silmaril.Formats.Parquet.Footer.PageLessInt32

/-- All framed groups pass the original strict footer validation with their
metadata intact and the total file row count unchanged. -/
theorem validate_framed {limits : Footer.Limits} {depth : Nat} {source : Bytes}
    {span : Footer.Span} {metadata : Footer.Metadata}
    (admitted : validate limits depth source span metadata = .ok ()) :
    Footer.validate span.start depth
      { metadata with rowGroups := metadata.rowGroups.filter (!isPageLess ·) } = .ok () :=
  Proofs.Formats.Parquet.Footer.PageLessInt32.validate_framed admitted

/-- Only zero rows and zero bytes can be removed from that validation projection. -/
theorem pageLess_zero {group : Footer.RowGroup} (empty : isPageLess group = true) :
    group.numRows = 0 ∧ group.totalByteSize = 0 :=
  Proofs.Formats.Parquet.Footer.PageLessInt32.pageLess_zero empty

end Silmaril.Formats.Parquet.Footer.PageLessInt32
