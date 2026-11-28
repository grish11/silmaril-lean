module

import Silmaril.Formats.Parquet.FlatColumn.Zstd.Thms
import Batteries.Data.Except
meta import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs
meta import Batteries.Data.Except

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Compression.Zstd (rawFrame)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatColumn.Zstd

private def frame := rawFrame [97, 98, 99]
private def limits : CompressionLimits := ⟨1024, 64⟩
private def bounds : Payload.Bounds := ⟨frame.length, frame.length, 3, 3, 0⟩

#guard decodePayload limits bounds 6 frame = .ok [97, 98, 99]
#guard decodePayload limits ⟨3, 3, 3, 3, 0⟩ 0 [97, 98, 99] = .ok [97, 98, 99]
#guard decodePayload limits bounds 1 frame = .error (.codec 1)
#guard decodePayload limits bounds 6 frame.dropLast = .error (.scalar (.payload .compressedSizeMismatch))
#guard decodePayload limits bounds 6 (frame ++ [0]) = .error (.scalar (.payload .compressedSizeMismatch))
#guard decodePayload limits {bounds with expectedSize := 4, outputLimit := 4} 6 frame =
  .error (.scalar (.payload .outputSizeMismatch))
#guard decodePayload limits {bounds with compressedLimit := frame.length - 1} 6 frame =
  .error (.scalar (.payload .compressedLimit))
#guard decodePayload limits {bounds with outputLimit := 2} 6 frame = .error (.scalar (.payload .outputLimit))
#guard decodePayload limits {bounds with compressedSize := frame.length + 1, compressedLimit := frame.length + 1}
    6 (frame ++ [0]) = .error (.frame (.frame .trailingInput))
#guard decodePayload limits bounds 0 frame = .error (.scalar (.payload .outputSizeMismatch))

private def pageLimits : Limits := ⟨{}, ⟨16, 16, ⟨16, 16⟩, 0⟩, limits⟩
private def leaf : Footer.SchemaElement := ⟨some .int32, none, some .optional, "x", none⟩
private def metadata : Footer.ColumnMetadata :=
  ⟨.int32, [0, 3], ["x"], 6, 1, 1, 1, 4, none, none, none, none⟩
private def rawLevels : Page.Kind := .dataV2 ⟨1, 0, 1, 0, 2, 0, false⟩

#guard decodePage pageLimits .optional leaf metadata ⟨1, 2, none, rawLevels⟩ (Bytes.ofList [1, 2]) =
  .error (.scalar .invalidLevelExtent)
#guard decodePage pageLimits .optional leaf metadata ⟨2, 1, none, rawLevels⟩ (Bytes.ofList [1]) =
  .error (.scalar .invalidLevelExtent)
#guard decodePage pageLimits .optional leaf metadata ⟨2, 2, none, rawLevels⟩ (Bytes.ofList [1]) =
  .error (.scalar (.payload .compressedSizeMismatch))

#guard decodePage pageLimits .required {leaf with repetition := some .required} metadata
    ⟨4, frame.length, none, .dataV2 ⟨1, 0, 1, 0, 0, 0, false⟩⟩
    (Bytes.ofList frame) = .error (.scalar (.payload .outputSizeMismatch))
