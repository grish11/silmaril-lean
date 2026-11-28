module

public import Silmaril.Formats.Parquet.PlainV1Writer.Defs
import Silmaril.Proofs.Formats.Parquet.PlainV1Writer.Body
import Silmaril.Proofs.Formats.Parquet.PlainV1Writer.Emit

/-! Exact V1 header/body extents and ordered INT32 slot recovery. -/

public section

namespace Silmaril.Formats.Parquet.PlainV1Writer

theorem body_length (input : Input) : input.body.length = input.bodySize :=
  Proofs.Formats.Parquet.PlainV1Writer.body_length input

/-- The existing ScalarPage decoder recovers every slot within the same limits,
including all-null, mixed, and empty input. -/
theorem decode_body {input : Input} {limits : Limits} (fits : input.Fits limits) :
    ScalarPage.decode .int32 input.parameters limits.scalar input.body = .ok input.slots :=
  Proofs.Formats.Parquet.PlainV1Writer.decode_body fits

/-- The checked header parser consumes exactly the header prefix and both
size fields describe exactly the separate body. -/
theorem emit_exact {limits : Limits} {input : Input} {page : Encoded}
    (written : emit limits input = .ok page) :
    input.Fits limits ∧ page.headerBytes.length ≤ limits.headerBytes ∧
      page.header = input.header ∧ page.body = input.body ∧
      Page.readHeaderPrefix limits.header page.wire = .ok (page.header, page.headerBytes.length) ∧
      page.header.compressedSize = page.body.length ∧ page.header.uncompressedSize = page.body.length ∧
      page.wire.length = page.headerBytes.length + page.body.length :=
  Proofs.Formats.Parquet.PlainV1Writer.emit_exact written

theorem emit_roundTrip {limits : Limits} {input : Input} {page : Encoded}
    (written : emit limits input = .ok page) :
    ScalarPage.decode .int32 input.parameters limits.scalar page.body = .ok input.slots := by
  obtain ⟨fits, _, _, body, _⟩ := emit_exact written
  rw [body]
  exact decode_body fits

end Silmaril.Formats.Parquet.PlainV1Writer
