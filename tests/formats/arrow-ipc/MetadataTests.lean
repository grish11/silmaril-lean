module

import Silmaril.Formats.Arrow.Stream.Defs

open Silmaril Silmaril.Formats.Arrow

private def check (label : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError label)

private def packed (bytes : ByteArray) : KBytes :=
  .leaf bytes.size (KBytes.leVal bytes.data.toList)

private def expectFailure (label : String) (source : KBytes) (error : Error)
    (limits : Limits := {}) : IO Unit :=
  match readStream limits source with
  | .error actual => check s!"{label}: expected {repr error}, got {repr actual}" (actual == error)
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")

private def schema : List Field := [⟨"n", true, .int32⟩, ⟨"téxt", true, .utf8⟩]

private def batches : List RecordBatch :=
  [⟨4, [⟨4, 1⟩, ⟨4, 1⟩], [⟨0, 1⟩, ⟨8, 16⟩, ⟨24, 1⟩, ⟨32, 20⟩, ⟨56, 5⟩]⟩,
   ⟨0, [⟨0, 0⟩, ⟨0, 0⟩], [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 4⟩, ⟨8, 0⟩]⟩,
   ⟨1, [⟨1, 1⟩, ⟨1, 1⟩], [⟨0, 1⟩, ⟨8, 4⟩, ⟨16, 1⟩, ⟨24, 8⟩, ⟨32, 0⟩]⟩,
   ⟨1, [⟨1, 0⟩, ⟨1, 0⟩], [⟨0, 0⟩, ⟨0, 4⟩, ⟨8, 0⟩, ⟨8, 8⟩, ⟨16, 0⟩]⟩]

private def checkStream (bytes : ByteArray) (input : KBytes) (label : String) : IO Unit := do
  let stream ← match readStream {} input with
    | .ok stream => pure stream
    | .error reason => throw (IO.userError s!"{label}: {repr reason}")
  check (label ++ " schema") (stream.fields == schema)
  check (label ++ " ordered metadata") (stream.batches.map (·.metadata) == batches)
  let ranges := [(384, 448), (648, 656), (864, 896), (1104, 1120)]
  let bodies := ranges.map fun (first, stop) => (bytes.extract first stop).data.toList
  check (label ++ " exact bodies") (stream.batches.map (·.body.toList) == bodies)

private def patch (bytes : ByteArray) (offset width value : Nat) : KBytes :=
  packed <| ((KBytes.unpack width value).zipIdx).foldl
    (fun data (byte, index) => data.set! (offset + index) byte) bytes

public def main : IO Unit := do
  let bytes ← IO.FS.readBinFile "tests/formats/arrow-ipc/nullable-int32-utf8.arrows"
  check "fixture length" (bytes.size == 1128)
  let input := packed bytes
  for split in [:bytes.size + 1] do
    let left := packed (bytes.extract 0 split)
    let right := packed (bytes.extract split bytes.size)
    checkStream bytes (left ++ right) s!"split {split}"
  for stop in [:bytes.size] do
    expectFailure s!"truncation at {stop}" (packed (bytes.extract 0 stop)) (.malformed .truncated)
  let eos := packed (bytes.extract 1120 1128)
  let schemaFrame := packed (bytes.extract 0 176)
  expectFailure "no schema" eos (.malformed .schemaOrder)
  expectFailure "record batch first" (packed (bytes.extract 176 bytes.size)) (.malformed .schemaOrder)
  expectFailure "repeated schema" (schemaFrame ++ schemaFrame ++ eos) (.malformed .schemaOrder)
  expectFailure "trailing octet" (input ++ .leaf 1 0) (.malformed .trailingBytes)
  expectFailure "bad continuation" (patch bytes 0 4 0) (.malformed .continuation)
  expectFailure "legacy prefix" (patch bytes 0 4 168) (.unsupported .legacyFraming)
  expectFailure "negative length" (patch bytes 4 4 0x80000000) (.malformed .metadataLength)
  expectFailure "misaligned metadata length" (patch bytes 4 4 167) (.malformed .metadataLength)
  expectFailure "invalid root offset" (patch bytes 8 4 0) (.malformed .flatbuffer)
  expectFailure "invalid vtable size" (patch bytes 14 2 9) (.malformed .flatbuffer)
  expectFailure "invalid vtable displacement" (patch bytes 24 4 0) (.malformed .flatbuffer)
  expectFailure "unsupported V4" (patch bytes 30 2 3) (.unsupported (.metadataVersion 3))
  expectFailure "missing message union tag" (patch bytes 29 1 0) (.malformed .flatbuffer)
  expectFailure "unknown message tag" (patch bytes 29 1 42) (.unsupported (.messageKind 42))
  expectFailure "unknown field type tag" (patch bytes 71 1 42) (.unsupported (.fieldType 42))
  expectFailure "field name UTF-8" (patch bytes 92 1 0xff) (.malformed .invalidUtf8)
  expectFailure "field name terminator" (patch bytes 97 1 1) (.malformed .flatbuffer)
  expectFailure "non-boolean nullable" (patch bytes 70 1 2) (.malformed .flatbuffer)
  expectFailure "negative body length" (patch bytes 216 8 (2^63)) (.malformed .bodyLength)
  expectFailure "misaligned body length" (patch bytes 216 8 63) (.malformed .bodyLength)
  expectFailure "vector exceeds metadata" (patch bytes 260 4 0xffffffff) (.malformed .flatbuffer)
  expectFailure "missing buffer descriptor" (patch bytes 260 4 4) (.malformed .batchLayout)
  expectFailure "short field node" (patch bytes 352 8 3) (.malformed .batchLayout)
  expectFailure "excess null count" (patch bytes 360 8 5) (.malformed .batchLayout)
  expectFailure "null in required field" (patch bytes 130 1 0) (.malformed .batchLayout)
  expectFailure "misaligned buffer offset" (patch bytes 280 8 9) (.malformed .batchLayout)
  expectFailure "overlapping buffers" (patch bytes 280 8 0) (.malformed .batchLayout)
  expectFailure "buffer exceeds body" (patch bytes 336 8 16) (.malformed .batchLayout)
  expectFailure "metadata byte cap" input (.limit .metadataBytes) { metadataBytes := 167 }
  expectFailure "body byte cap" input (.limit .bodyBytes) { bodyBytes := 63 }
  expectFailure "field cap" input (.limit .fields) { fields := 1 }
  expectFailure "row cap" input (.limit .rows) { rows := 3 }
  expectFailure "batch cap" input (.limit .batches) { batches := 3 }
  let .ok zeroBatches := readStream { batches := 0 } (schemaFrame ++ eos)
    | throw (IO.userError "schema and EOS should fit a zero batch cap")
  check "schema-only stream" (zeroBatches.fields == schema && zeroBatches.batches.isEmpty)
  IO.println "Arrow IPC V5 metadata: 1129 split points, 1128 truncations, and malformed, unsupported and limit cases passed"
