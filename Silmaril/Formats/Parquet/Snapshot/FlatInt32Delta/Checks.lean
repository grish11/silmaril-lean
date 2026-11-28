module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.FlatScan.Delta.Thms
import Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta.Defs

/-! Independent full-file V1/V2 readback and first-error coordinates. -/

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta

open Silmaril.Relational Silmaril.Formats.Arrow

private def v1 : Bytes := ⟨include_bytes "../../../../../data/parquet-flat-delta/plain-delta-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../data/parquet-flat-delta/plain-delta-v2.parquet"⟩
private def badCount : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-flat-delta/plain-delta-v2-bad-count.parquet"⟩
private def crc : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/crc-plain-v2.parquet"⟩
private def snappy : Bytes :=
  ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/snappy-plain-v2.parquet"⟩

private def schema : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩

private def observe {ε : Type} (stream : Events.EventStream String FlatInt32.Cell ε) :
    Except ε (List Nat × List (List (Option Int32)) × Events.Termination ε) :=
  stream.map fun ⟨_, trace⟩ => (trace.batches.map (·.rowCount), trace.rows.map List.ofFn, trace.termination)

private def read (bytes : Bytes) := observe (readAll {} schema bytes)

private def rows (n : Nat) : List (List (Option Int32)) := (List.range n).map fun (i : Nat) =>
  [some (Int32.ofInt ((i : Int) - 8)), if i % 4 == 1 then none else some (Int32.ofInt (300 - (i : Int) * i))]

#guard read v1 = .ok ([8, 8, 8], rows 24, .eos)
#guard read v2 = .ok ([8, 8, 8], rows 24, .eos)

#guard badCount.data == v2.data.set! 336 0
#guard read badCount = .ok ([8], rows 8, .readError
  (.decode 1 (.column 1 "optional_i32" (.atPage 1 307 (.decoder (.delta (.binaryPacked .countMismatch)))))))

-- A supported footer can neither authorize an unknown page tag nor substitute
-- its advertised tag for a different one in the original checked header.
private def changePageTag (encoded : UInt8) : Bytes := ⟨v2.data.set! 321 encoded⟩
#guard v2.data[321]! == 10
#guard read (changePageTag 14) = .ok ([8], rows 8, .readError
  (.decode 1 (.column 1 "optional_i32" (.atPage 1 307 .unsupportedPageEncoding))))
#guard read (changePageTag 0) = .ok ([8], rows 8, .readError
  (.decode 1 (.column 1 "optional_i32" (.atPage 1 307 .unsupportedPageEncoding))))

#guard read crc = .ok ([], [], .readError
  (.decode 0 (.column 0 "required_i32" (.atPage 0 4 .crcUnsupported))))
#guard read snappy = .ok ([], [], .readError
  (.decode 0 (.column 0 "required_i32" (.column (.columnCodec "required_i32")))))
#guard observe (readAll {packed := ⟨128, 2, 128, 4, 1⟩} schema v2) = .ok ([], [], .readError
  (.decode 0 (.column 1 "optional_i32" (.atPage 0 84 (.decoder (.delta (.binaryPacked .valueLimit)))))))
#guard observe (FlatInt32.readAll {} schema v2) = .ok ([], [], .readError
  (.decode 0 (.profile (.columnEncoding "optional_i32"))))

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Delta
