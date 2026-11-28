module

public import Silmaril.Formats.ColumnarTimestamp.Wire.Defs
import Silmaril.Proofs.Formats.ColumnarTimestamp.Wire.RoundTrip

/-! # Round trips for little-endian signed timestamp slices -/

public section

namespace Silmaril.Formats.ColumnarTimestamp.Wire

open Numeric.Timestamp

variable {kind : Kind} {source target : TickUnit}

/-- Encoding and decoding preserve the ordered, same-kind nanosecond denotations. -/
theorem decodeLE_encodeLE {values : List (Ticks kind source)} {bytes : Bytes}
    (encoded : encodeLE target values = .ok bytes) :
    (decodeLE kind target values.length bytes).map (List.map Ticks.denote) =
      .ok (values.map Ticks.denote) :=
  Proofs.Formats.ColumnarTimestamp.Wire.decodeLE_encodeLE encoded

/-- The batch writer succeeds exactly when every value has exact signed Int64 ticks. -/
theorem encodeLE_isSome_iff (values : List (Ticks kind source)) :
    (encodeLE target values).toOption.isSome = true ↔
      ∀ value ∈ values, (value.toInt64 target).toOption.isSome = true :=
  Proofs.Formats.ColumnarTimestamp.Wire.encodeLE_isSome_iff values

/-- Every accepted slice has the requested count and re-encodes byte for byte. -/
theorem encodeLE_decodeLE {bytes : Bytes} {count : Nat} {values : List (Ticks kind target)}
    (decoded : decodeLE kind target count bytes = .ok values) :
    values.length = count ∧ encodeLE target values = .ok bytes :=
  Proofs.Formats.ColumnarTimestamp.Wire.encodeLE_decodeLE decoded

end Silmaril.Formats.ColumnarTimestamp.Wire
