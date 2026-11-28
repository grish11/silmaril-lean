module

import Silmaril.Formats.Parquet.FlatColumn.Defs
import Silmaril.Formats.Parquet.ScalarPage.BrotliRaw.Defs
meta import Silmaril.Formats.Parquet.FlatColumn.Defs
meta import Silmaril.Formats.Parquet.ScalarPage.BrotliRaw.Defs

open Silmaril.Formats Silmaril.Formats.Parquet

private def requireIO {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def expectError (label : String) (expected : ScalarPage.BrotliRaw.Error)
    (result : Except ScalarPage.BrotliRaw.Error (List UInt8)) : IO Unit := do
  if let .error observed := result then
    if observed = expected then
      IO.println label
      return
    throw (IO.userError s!"{label}: wanted {reprStr expected}, got {reprStr observed}")
  throw (IO.userError s!"{label}: expected rejection")

private def testV1 (params : ScalarPage.Parameters) (body : Bytes) (pageLimits : ScalarPage.Limits)
    (limits : ScalarPage.BrotliRaw.Limits) : IO Unit := do
  let decode := ScalarPage.BrotliRaw.decodePage
  let check := decode limits pageLimits
  let sizes := params.sizes
  expectError "wrong-codec" (.codec 6) (check { params with codec := 6 } body)
  expectError "declared-input" (.page (.payload .compressedSizeMismatch))
    (check { params with sizes := { sizes with compressed := sizes.compressed - 1 } } body)
  expectError "declared-output-small" (.page (.payload .outputSizeMismatch))
    (check { params with sizes := { sizes with uncompressed := sizes.uncompressed - 1 } } body)
  expectError "declared-output-large" (.page (.payload .outputSizeMismatch))
    (decode limits { pageLimits with uncompressedBytes := sizes.uncompressed + 1 }
      { params with sizes := { sizes with uncompressed := sizes.uncompressed + 1 } } body)
  expectError "input-cap" (.page (.payload .compressedLimit))
    (decode limits { pageLimits with compressedBytes := sizes.compressed - 1 } params body)
  expectError "output-cap" (.page (.payload .outputLimit))
    (decode limits { pageLimits with uncompressedBytes := sizes.uncompressed - 1 } params body)
  expectError "window-cap" (.stream .windowLimit) (decode { limits with window := 0 } pageLimits params body)
  expectError "step-cap" (.stream .stepLimit) (decode { limits with steps := 1 } pageLimits params body)
  expectError "truncated" (.stream .truncated)
    (check { params with sizes := { sizes with compressed := sizes.compressed - 1 } }
      (Bytes.ofList (body.toList.take (sizes.compressed - 1))))
  expectError "trailing" (.stream .trailingInput)
    (decode limits { pageLimits with compressedBytes := sizes.compressed + 1 }
      { params with sizes := { sizes with compressed := sizes.compressed + 1 } }
      (Bytes.ofList (body.toList ++ [0])))
  match Payload.decode (pageLimits.payloadBounds sizes 0) 4 body.toList with
  | .error (.unsupportedCodec 4) => IO.println "default-codec-4"
  | _ => throw (IO.userError "default payload did not report unsupported codec 4")

private def testV2 (params : ScalarPage.Parameters) (body : Bytes) (pageLimits : ScalarPage.Limits)
    (limits : ScalarPage.BrotliRaw.Limits) : IO Unit := do
  let .v2 nulls rows repetitions definitions flag := params.version |
    throw (IO.userError "expected V2")
  let check := ScalarPage.BrotliRaw.decodePage limits pageLimits
  let sizes := params.sizes
  expectError "levels-over-input" (.page .invalidLevelExtent)
    (check { params with sizes := { sizes with compressed := definitions - 1 } }
      (Bytes.ofList (body.toList.take (definitions - 1))))
  expectError "levels-over-output" (.page .invalidLevelExtent)
    (check { params with sizes := { sizes with uncompressed := definitions - 1 } } body)
  if flag.getD true then
    expectError "false-flag-on-compressed" (.page (.payload .outputSizeMismatch))
      (check { params with version := .v2 nulls rows repetitions definitions (some false) } body)
  else
    expectError "true-flag-on-raw" (.stream .reservedMetadata)
      (check { params with version := .v2 nulls rows repetitions definitions (some true) } body)

public def main (args : List String) : IO UInt32 := do
  let [file, expectedPath, control] := args | return 2
  let source : Bytes := ⟨← IO.FS.readBinFile file⟩
  let snapshot ← requireIO (Snapshot.check (Failure := Unit) {} source)
  let some group := snapshot.groupAt 0 | return 2
  let [column] := group.columns | return 2
  let some leaf := snapshot.metadata.schema[1]? | return 2
  let layout : FlatColumn.Layout ← match leaf.repetition with
    | some .required => pure .required
    | some .optional => pure .optional
    | _ => throw (IO.userError "expected a flat leaf")
  let some span := Page.columnSpan snapshot.footer.start column.metadata | return 2
  let [frame] ← requireIO (Page.readChunk {} source span) | return 2
  let some params := FlatColumn.pageParameters layout column.metadata.codec frame.value | return 2
  let body := FlatColumn.frameBody source frame
  let pageLimits : ScalarPage.Limits := ⟨params.sizes.compressed, params.sizes.uncompressed, ⟨262144, 1048576⟩, 0⟩
  -- A raw V2 suffix must succeed without any Brotli window or step budget.
  let limits : ScalarPage.BrotliRaw.Limits := if control = "raw" then ⟨0, 0⟩ else ⟨2 ^ 24 - 16, 8⟩
  let decoded := ScalarPage.BrotliRaw.decodePage limits pageLimits params body
  if control = "entropy" then
    expectError "unsupportedCompressed" (.stream .unsupportedCompressed) decoded
  else if control = "metadata" then
    expectError "unsupportedMetadata" (.stream .unsupportedMetadata) decoded
  else
    let actual ← requireIO decoded
    let expected ← IO.FS.readBinFile expectedPath
    if actual ≠ expected.data.toList then throw (IO.userError "expanded body differs from the independent oracle")
    IO.println s!"{frame.payload.start} {frame.payload.stop} {actual.length}"
    if control = "v1" then testV1 params body pageLimits limits
    if control = "v2" then testV2 params body pageLimits limits
    if control = "raw" then testV2 params body pageLimits ⟨2 ^ 24 - 16, 8⟩
  return 0
