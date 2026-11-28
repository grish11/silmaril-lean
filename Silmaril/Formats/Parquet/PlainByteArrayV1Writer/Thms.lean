module

public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.Defs
import Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer.Correctness

/-! Checked bounds, exact V1 framing, and nullable BYTE_ARRAY readback. -/

public section

namespace Silmaril.Formats.Parquet.PlainByteArrayV1Writer

/-- Each optional definition slot uses one two-octet width-one RLE run. -/
theorem definition_length (mask : List Bool) : (definitionOctets mask).length = 2 * mask.length :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.definition_length mask

/-- The body size includes the entire level prefix and PLAIN scalar slice. -/
theorem body_length (input : Input) {scalars : Bytes} (size : scalars.length = Plain.ByteArray.encodedSize input.values) :
    (input.body scalars).length = input.bodySize :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.body_length input size

/-- The shared reader recovers the exact definition mask and the original scalar suffix. -/
theorem prepare_body {input : Input} {limits : Limits} {scalars : Bytes} (fits : input.Fits limits)
    (size : scalars.length = Plain.ByteArray.encodedSize input.values) :
    ScalarPage.prepare input.parameters limits.page.scalar (input.body scalars) =
      .ok ⟨input.slots.map Option.isSome, scalars⟩ :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.prepare_body fits size

/-- Successful emission uses the checked Compact header and PLAIN scalar serializer.
The header and body extents describe every returned octet. -/
theorem emit_exact {limits : Limits} {input : Input} {page : Encoded} (written : emit limits input = .ok page) :
    input.Fits limits ∧ page.headerBytes.length ≤ limits.page.headerBytes ∧
      PlainV1Writer.encodeHeader input.numValues input.bodySize = some page.headerBytes ∧
      page.header = input.header ∧
      Page.readHeaderPrefix limits.page.header page.wire = .ok (page.header, page.headerBytes.length) ∧
      page.header.compressedSize = page.body.length ∧ page.header.uncompressedSize = page.body.length ∧
      page.wire.length = page.headerBytes.length + page.body.length ∧
      ∃ scalars, Plain.ByteArray.encode limits.plain input.values = .ok scalars ∧ page.body = input.body scalars :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.emit_exact written

/-- Emitted bodies prepare to the exact mask and the successful PLAIN encoding of present values. -/
theorem emit_prepared {limits : Limits} {input : Input} {page : Encoded} (written : emit limits input = .ok page) :
    ∃ scalars, Plain.ByteArray.encode limits.plain input.values = .ok scalars ∧
      ScalarPage.prepare input.parameters limits.page.scalar page.body =
        .ok ⟨input.slots.map Option.isSome, scalars⟩ :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.emit_prepared written

/-- The standard scalar reader recovers every original slot in order, including null and empty bytes. -/
theorem emit_roundTrip {limits : Limits} {input : Input} {page : Encoded}
    (written : emit limits input = .ok page) :
    ScalarPage.decode (.byteArray limits.plain) input.parameters limits.page.scalar page.body = .ok input.slots :=
  Proofs.Formats.Parquet.PlainByteArrayV1Writer.emit_roundTrip written

end Silmaril.Formats.Parquet.PlainByteArrayV1Writer
