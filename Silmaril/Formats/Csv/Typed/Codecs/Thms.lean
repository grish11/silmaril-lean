module

public import Silmaril.Formats.Csv.Typed.Codecs.Defs
import Silmaril.Proofs.Formats.Csv.CellCodecs

/-! # Exact decimal and UTF-8 cell codec laws -/

public section

namespace Silmaril.Formats.Csv.Typed.Codecs

/-- Accepted text is exactly the canonical decimal of the returned Int32. -/
theorem parseInt32_eq_some_iff (field : Field) (value : Int32) :
    parseInt32 field = some value ↔ DecimalSpelling field value.toInt :=
  Proofs.Formats.Csv.CellCodecs.parseInt32_eq_some_iff field value

/-- Int32 parsing recovers every successfully printed value. -/
theorem int32_parsePrint : int32.ParsePrint := Proofs.Formats.Csv.CellCodecs.int32_parsePrint

/-- Int32 printing recovers every successfully parsed spelling. -/
theorem int32_printParse : int32.PrintParse := Proofs.Formats.Csv.CellCodecs.int32_printParse

/-- Every Int32 decimal fits the lexical CSV field alphabet. -/
theorem int32_textBytesOK (value : Int32) : textBytesOK (int32Text value) = true :=
  Proofs.Formats.Csv.CellCodecs.int32_textBytesOK value

/-- Parsing succeeds exactly on the CSV field alphabet. -/
theorem utf8_parse_isSome_iff (field : Field) :
    (utf8.parse field).isSome = true ↔ textBytesOK field = true :=
  Proofs.Formats.Csv.CellCodecs.utf8_parse_isSome_iff field

/-- Printing succeeds exactly when the original UTF-8 bytes are representable. -/
theorem utf8_print_eq_some_iff (value : String) (field : Field) :
    utf8.print value = some field ↔ field = value.toByteArray.data.toList ∧ textBytesOK field = true :=
  Proofs.Formats.Csv.CellCodecs.utf8_print_eq_some_iff value field

/-- UTF-8 parsing recovers every successfully printed string. -/
theorem utf8_parsePrint : utf8.ParsePrint := Proofs.Formats.Csv.CellCodecs.utf8_parsePrint

/-- UTF-8 printing recovers every successfully parsed byte list. -/
theorem utf8_printParse : utf8.PrintParse := Proofs.Formats.Csv.CellCodecs.utf8_printParse

end Silmaril.Formats.Csv.Typed.Codecs
