module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.FlatScan.Snappy.Thms
import Silmaril.Formats.Parquet.Snapshot.FlatInt32Snappy.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32Snappy.Defs

/-! Full-file V1/V2 readback and typed failure locations on independent files. -/

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Snappy

open Silmaril.Relational Silmaril.Formats.Arrow

private def v1 : Bytes := ⟨include_bytes "../../../../../data/parquet-flat-snappy/snappy-plain-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../data/parquet-flat-snappy/snappy-plain-v2.parquet"⟩
private def badV1 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-flat-snappy/snappy-plain-v1-bad-size.parquet"⟩
private def badV2 : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-flat-snappy/snappy-plain-v2-bad-size.parquet"⟩
private def rawFile : Bytes := ⟨include_bytes "../../../../../data/parquet-flat-delta/plain-delta-v2.parquet"⟩

private def schema : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩

private def rows (n : Nat) : List (List (Option Int32)) := (List.range n).map fun (i : Nat) =>
  [some (Int32.ofInt (-(Int.ofNat (i / 16)))),
    if i % 4 == 1 then none
    else if i / 32 == 1 then some 300
    else some (Int32.ofInt ((Int.ofNat i * 1640531527 + 13011) % 2^32 - 2^31))]

private def observe {ε : Type} (stream : Events.EventStream String FlatInt32.Cell ε) :
    Except ε (List Nat × List (List (Option Int32)) × Events.Termination ε) :=
  stream.map fun ⟨_, trace⟩ => (trace.batches.map (·.rowCount), trace.rows.map List.ofFn, trace.termination)

private def read (bytes : Bytes) := observe (readAll {} schema bytes)

#guard read v1 = .ok ([32, 32, 32], rows 96, .eos)
#guard read v2 = .ok ([32, 32, 32], rows 96, .eos)

private def damaged (header : Nat) : Snapshot.Error Error :=
  .decode 1 (.column 1 "optional_i32" (.atPage 1 header (.decoder (.scalar (.payload .outputSizeMismatch)))))

#guard v1.data[320]! == 55 && badV1.data == v1.data.set! 320 56
#guard v2.data[347]! == 48 && badV2.data == v2.data.set! 347 49
#guard read badV1 = .ok ([32], rows 32, .readError (damaged 301))
#guard read badV2 = .ok ([32], rows 32, .readError (damaged 320))

-- The first optional V2 page carries raw values. Increase just the declared
-- expanded size. The checked header must reject the unequal raw extents.
#guard v2.data[69]! == 102
#guard read ⟨v2.data.set! 69 104⟩ = .ok ([], [], .readError
  (.decode 0 (.column 1 "optional_i32" (.column (.page (.header .invalidV2Lengths))))))

-- Keep the value and level allowlists tied to the original page headers.
#guard v2.data[334]! == 0
#guard read ⟨v2.data.set! 334 10⟩ = .ok ([32], rows 32, .readError
  (.decode 1 (.column 1 "optional_i32" (.atPage 1 320 .unsupportedPageEncoding))))
#guard v1.data[68]! == 6
#guard read ⟨v1.data.set! 68 8⟩ = .ok ([], [], .readError
  (.decode 0 (.column 1 "optional_i32" (.atPage 0 56 .unsupportedPageEncoding))))

#guard read rawFile = .ok ([], [], .readError
  (.decode 0 (.column 0 "required_i32" (.column (.columnCodec "required_i32")))))
#guard observe (FlatInt32.readAll {} schema v2) = .ok ([], [], .readError
  (.decode 0 (.profile (.columnCodec "required_i32"))))

private def firstPageError (reason : FlatScan.Error FlatScan.AdapterError) : Snapshot.Error Error :=
  .decode 0 (.column 0 "required_i32" (.atPage 0 4 reason))

private def defaults : Limits := {}

#guard observe (readAll {defaults with flat.groups.maxPageBytes := 63} schema v1) =
  .ok ([], [], .readError (firstPageError .pageByteLimit))
#guard observe (readAll {defaults with flat.pages.compressedBytes := 5} schema v1) =
  .ok ([], [], .readError (firstPageError (.decoder (.scalar (.payload .compressedLimit)))))
#guard observe (readAll {defaults with flat.pages.uncompressedBytes := 63} schema v1) =
  .ok ([], [], .readError (firstPageError (.decoder (.scalar (.payload .outputLimit)))))

-- A PLAIN V1 frame with an explicit CRC and no body. The codec is Snappy,
-- and the rejecting scanner should report the CRC before trying to decode.
private def crcRejected : Except (FlatScan.ColumnFailure Unit) Unit := do
  let (_, metadata) ← (Footer.readFooter {} v1).mapError (.column ∘ .footer)
  let some first := metadata.rowGroups.head?.bind (·.columns.head?) | throw (.column .groupIndex)
  let bytes := Bytes.ofList [0, 0, 0, 0, 0x15, 0, 0x15, 0, 0x15, 0, 0x15, 0, 0x1c,
    0x15, 2, 0x15, 0, 0x15, 6, 0x15, 6, 0, 0]
  let change := {first.metadata with
    numValues := 1
    totalCompressedSize := Int.ofNat (bytes.length - 4)}
  let col := {first with metadata := change}
  let decode : FlatScan.DecodePage Unit := fun _ _ _ => .error ()
  (FlatScan.scanColumnSnappy {} decode bytes bytes.length ⟨"required_i32", .required⟩ 1 col).map (fun _ => ())

#guard crcRejected = .error (.atPage 0 4 .crcUnsupported)

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Snappy
