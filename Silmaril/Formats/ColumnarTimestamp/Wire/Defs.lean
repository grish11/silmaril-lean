module

public import Silmaril.Formats.ColumnarTimestamp.Defs
public import Silmaril.Formats.Parquet.Plain.Defs

/-! # Exact little-endian signed timestamp value slices -/

@[expose] public section

namespace Silmaril.Formats.ColumnarTimestamp

open Numeric.Timestamp
open Silmaril.Formats.Parquet

namespace Wire

/-- Decode one exact slice of little-endian signed Int64 values. The kind and
unit are supplied by the checked schema, and `count` counts physical values. -/
def decodeLE (kind : Kind) (unit : TickUnit) (count : Nat) (bytes : Bytes) :
    Except Plain.Error (List (Ticks kind unit)) :=
  (Plain.decodeInt64 count bytes).map (List.map (Ticks.ofInt64 kind unit))

/-- Rescale every value exactly and check the signed Int64 range before producing bytes. -/
def encodeLE {kind : Kind} {source : TickUnit} (target : TickUnit)
    (values : List (Ticks kind source)) : Except ConversionError Bytes :=
  (values.mapM (fun value => Ticks.toInt64 value target)).map Plain.encodeInt64

end Wire

namespace Arrow.Metadata

/-- Decode the delimited little-endian Arrow values buffer. Validity, byte
order, external padding and buffer bounds are the caller's responsibility. -/
abbrev decodeBufferLE (metadata : Arrow.Metadata) (count : Nat) (bytes : Bytes) :
    Except Plain.Error (List (Ticks metadata.kind metadata.unit)) :=
  Wire.decodeLE metadata.kind metadata.unit count bytes

/-- Encode the unpadded Arrow values buffer for this little-endian schema. -/
abbrev encodeBufferLE (metadata : Arrow.Metadata) {source : TickUnit}
    (values : List (Ticks metadata.kind source)) : Except ConversionError Bytes :=
  Wire.encodeLE metadata.unit values

end Arrow.Metadata

namespace Parquet.Metadata

/-- Decode the delimited INT64 PLAIN values. The count excludes entries with no
physical value as determined by the definition levels. -/
abbrev decodePlain (metadata : Parquet.Metadata) (count : Nat) (bytes : Bytes) :
    Except Plain.Error (List (Ticks metadata.kind metadata.unit.tickUnit)) :=
  Wire.decodeLE metadata.kind metadata.unit.tickUnit count bytes

/-- Encode the INT64 PLAIN values stream before page framing. -/
abbrev encodePlain (metadata : Parquet.Metadata) {source : TickUnit}
    (values : List (Ticks metadata.kind source)) : Except ConversionError Bytes :=
  Wire.encodeLE metadata.unit.tickUnit values

end Parquet.Metadata

end Silmaril.Formats.ColumnarTimestamp
