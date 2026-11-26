module

public import Silmaril.Formats.Csv.Utf8.Defs
import Silmaril.Proofs.Formats.Csv.Utf8

/-! # Correctness of the UTF-8 CSV profile -/

public section

namespace Silmaril.Formats.Csv.Utf8

/-- Both decoders give the same result on every ASCII input, including malformed CSV. -/
theorem decode_eq_ascii (wire : Bytes) (ascii : ∀ b ∈ wire, b < 0x80) :
    decode wire = Csv.decode wire :=
  Proofs.Formats.Csv.Utf8.decode_eq_ascii wire ascii

/-- Both encoders give the same result for ASCII fields, including unrepresentable rows. -/
theorem encode_eq_ascii (rows : Rows)
    (ascii : ∀ row ∈ rows, ∀ field ∈ row, ∀ b ∈ field, b < 0x80) :
    encode rows = Csv.encode rows :=
  Proofs.Formats.Csv.Utf8.encode_eq_ascii rows ascii

/-- A successful export round-trips exactly, including every UTF-8 byte. -/
theorem decode_encode {rows : Rows} {wire : Bytes} (h : encode rows = some wire) :
    decode wire = some rows :=
  Proofs.Formats.Csv.Utf8.decode_encode h

/-- Every field returned by the decoder is valid UTF-8. -/
theorem decode_fields_utf8 {wire : Bytes} {rows : Rows} (h : decode wire = some rows) :
    ∀ row ∈ rows, ∀ field ∈ row, (⟨field.toArray⟩ : ByteArray).IsValidUTF8 :=
  Proofs.Formats.Csv.Utf8.decode_fields_utf8 h

end Silmaril.Formats.Csv.Utf8
