module

import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Thms
import Silmaril.Formats.Csv.Typed.Codecs.Thms
meta import Silmaril.Formats.Arrow.TimestampStream.ToCsv.Defs

namespace Silmaril.Formats.Arrow.TimestampStream.ToCsv

open Silmaril.Numeric.Timestamp

private def bytes (text : String) : Csv.Bytes := text.toByteArray.data.toList
private def original : TimestampBatch.Binding := ⟨"time", true, ⟨.nanosecond, some "Asia/Kathmandu"⟩⟩
private def declared : Kind := ⟨.nanosecond, some "Asia/Kathmandu", true⟩

private def endpoints : Csv.Bytes :=
  bytes "time\r\nT-9223372036854775808\r\nN\r\nT9223372036854775807\r\n"

#guard (schemaOf original).kind ⟨0, by simp [schemaOf]⟩ == (bytes "time", declared)
#guard (Csv.Typed.Utf8.decode (schemaOf original) codecs endpoints).toOption.map
  (List.map fun row => (row ⟨0, by simp [schemaOf]⟩).map Ticks.ticks) ==
    some [some (-9223372036854775808), none, some 9223372036854775807]
#guard (codecs declared).parse (bytes "9223372036854775808") == none
#guard (codecs declared).parse (bytes "-9223372036854775809") == none
#guard (codecs declared).parse (bytes "-0") == none
#guard (codecs declared).parse (bytes "01") == none
#guard (codecs declared).parse (bytes "+1") == none

#print axioms Csv.Typed.Codecs.parseInt64_eq_some_iff
#print axioms Csv.Typed.Codecs.int64_parsePrint
#print axioms Csv.Typed.Codecs.int64_printParse
#print axioms codecs_parsePrint
#print axioms rows_order
#print axioms convert_read_error
#print axioms convert_of_read
#print axioms convert_readback

end Silmaril.Formats.Arrow.TimestampStream.ToCsv
