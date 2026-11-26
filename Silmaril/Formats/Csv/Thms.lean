module

public import Silmaril.Formats.Csv.Defs
import Silmaril.Proofs.Formats.Csv.Codec

/-! # Correctness of the RFC 4180 byte profile -/

public section

namespace Silmaril.Formats.Csv

/-- Decoding succeeds exactly for the rows related to the whole input by the byte grammar. -/
theorem decode_eq_some_iff (input : Bytes) (rows : Rows) :
    decode input = some rows ↔ Parses input rows :=
  Proofs.Formats.Csv.decode_eq_some_iff input rows

/-- The byte grammar produces only nonempty rows of representable fields. -/
theorem parses_wellFormed {wire : Bytes} {rows : Rows} (h : Parses wire rows) : WellFormed rows :=
  Proofs.Formats.Csv.parses_wellFormed h

/-- The encoder rejects exactly the unrepresentable row sequences. -/
theorem encode_eq_none_iff (rows : Rows) : encode rows = none ↔ ¬ WellFormed rows :=
  Proofs.Formats.Csv.encode_eq_none_iff rows

/-- Every successful encoding satisfies the byte grammar for the supplied rows. -/
theorem encode_sound {rows : Rows} {wire : Bytes} (h : encode rows = some wire) : Parses wire rows :=
  Proofs.Formats.Csv.encode_sound h

/-- Decoding a successful encoding recovers the ordered rows and each field byte. -/
theorem decode_encode {rows : Rows} {wire : Bytes} (h : encode rows = some wire) :
    decode wire = some rows :=
  (decode_eq_some_iff wire rows).mpr (encode_sound h)

end Silmaril.Formats.Csv
