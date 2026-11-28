module

public import Silmaril.Formats.Csv.Typed.Utf8.Defs
import Silmaril.Formats.Csv.Utf8.Thms
import Silmaril.Proofs.Formats.Csv.TypedUtf8

/-! # Round trips for typed UTF-8 CSV -/

public section

namespace Silmaril.Formats.Csv.Typed.Utf8

/-- The string codec parses the original UTF-8 bytes back to the string. -/
theorem string_parsePrint : string.ParsePrint :=
  Proofs.Formats.Csv.TypedUtf8.string_parsePrint

/-- The string codec prints the exact successfully parsed UTF-8 bytes. -/
theorem string_printParse : string.PrintParse :=
  Proofs.Formats.Csv.TypedUtf8.string_printParse

variable {Kind : Type*} {Value : Kind → Type*} {schema : Schema Kind}
variable {codecs : (kind : Kind) → CellCodec (Value kind)}

/-- A successful wire export round-trips the ordered nullable table. -/
theorem decode_encode (law : ∀ k, (codecs k).ParsePrint)
    {table : Table schema Value} {wire : Bytes} (h : encode schema codecs table = .ok wire) :
    decode schema codecs wire = .ok table :=
  Proofs.Formats.Csv.TypedUtf8.decode_encode law h

/-- Re-encoding a successful import preserves the exact lexical rows. -/
theorem encode_of_decode (law : ∀ k, (codecs k).PrintParse)
    {table : Table schema Value} {input : Bytes} (h : decode schema codecs input = .ok table) :
    ∃ output, encode schema codecs table = .ok output ∧ Csv.Utf8.decode output = Csv.Utf8.decode input :=
  Proofs.Formats.Csv.TypedUtf8.encode_of_decode law h

/-- With identical cell codecs, the two typed decoders agree on ASCII input. -/
theorem decode_eq_ascii (wire : Bytes) (ascii : ∀ b ∈ wire, b < 0x80) :
    decode schema codecs wire = Typed.decode schema codecs wire := by
  rw [decode, Typed.decode, Csv.Utf8.decode_eq_ascii wire ascii]
  cases Csv.decode wire <;> rfl

/-- With identical cell codecs, the two typed encoders agree on ASCII lexical exports. -/
theorem encode_eq_ascii (table : Table schema Value)
    (ascii : ∀ rows, exportRows schema codecs table = .ok rows →
      ∀ row ∈ rows, ∀ field ∈ row, ∀ b ∈ field, b < 0x80) :
    encode schema codecs table = Typed.encode schema codecs table :=
  Proofs.Formats.Csv.TypedUtf8.encode_eq_ascii table ascii

end Silmaril.Formats.Csv.Typed.Utf8
