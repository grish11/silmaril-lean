module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.FromCsv.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Defs

namespace Silmaril.Formats.Csv.ParquetIpc.FromIpc

open Silmaril.Relational
open Silmaril.Formats.Parquet
open Silmaril.Formats.Relational.NamedTable (Packed)
open Snapshot.FlatInt32 (Cell)
open Snapshot.FlatInt32.ToCsv (csvSchema)

private def multiBytes : ByteArray :=
  include_bytes "../../../../../tests/formats/arrow-ipc-to-parquet/multi-batch.arrows"

private def zeroBytes : ByteArray :=
  include_bytes "../../../../../tests/formats/arrow-ipc-to-parquet/zero-rows.arrows"

private def asIpc (bytes : ByteArray) : KBytes :=
  KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)

private def multi := asIpc multiBytes
private def zero := asIpc zeroBytes
private def schema : Scan.Schema String Unit := ⟨2, fun i => (if i.val = 0 then "café" else "値", ())⟩
private def reversed : Scan.Schema String Unit := ⟨2, fun i => (if i.val = 0 then "値" else "café", ())⟩
private def db : Packed Nat Csv.Field Cell := fun name =>
  if name = 0 then some ⟨csvSchema schema, [fun _ => some 7]⟩ else none

private def limits : FlatInt32Writer.Limits := ⟨8, 16384, {}, ⟨{}, 64, ⟨4096, 4096, ⟨64, 512⟩, 0⟩⟩⟩

private def scanLimits (count : Nat) : FlatScan.Limits :=
  limits.scanLimits ⟨count, [⟨"café", .optional []⟩, ⟨"値", .optional []⟩]⟩

private def observeDb (database : Packed Nat Csv.Field Cell) (name : Nat) :
    Option (List Csv.Field × List (List (Option Int32))) :=
  (Scan.observePacked database name).map fun table =>
    ((List.ofFn fun i => (table.schema.kind i).1), table.rows.map List.ofFn)

private def observe (input : KBytes) (count : Nat) := do
  let result ← (convert db 1 schema {} limits input).toOption
  let batch ← (FlatScan.scanFileRowGroup (scanLimits count)
    (FlatScan.decodeInt32Page limits.page.scalar) result.bytes 0).toOption
  pure (batch.columns.map Prod.fst, batch.rows, batch.rowCount, observeDb result.db 1, observeDb result.db 0)

private def expected : List (List (Option Int32)) :=
  [[some (-2147483648), none], [none, some 0], [some 2147483647, some (-1)]]

private def columns : List FlatScan.Field := [⟨"café", .optional⟩, ⟨"値", .optional⟩]
private def labels := ["café".toByteArray.data.toList, "値".toByteArray.data.toList]
private def unchanged : Option (List Csv.Field × List (List (Option Int32))) := some (labels, [[some 7, some 7]])

#guard (Arrow.readRows {} multi).toOption.map (fun source => source.batches.map List.length) == some [2, 0, 1]
#guard observe multi 3 == some (columns, expected, 3, some (labels, expected), unchanged)
#guard observe zero 0 == some (columns, [], 0, some (labels, []), unchanged)

-- The last nonempty batch ends at byte 784, followed by the 8-byte EOS.
private def lateTruncation := multi.slice 0 783
private def missingEos := multi.slice 0 784

#guard (convert db 1 schema {} limits lateTruncation).map (·.bytes) =
  .error (.input (.ipc (.malformed .truncated)))
#guard (convert db 1 schema {} limits missingEos).map (·.bytes) =
  .error (.input (.ipc (.malformed .truncated)))
#guard (convert db 0 schema {} limits lateTruncation).map (·.bytes) = .error .nameConflict
#guard (convert db 1 reversed {} limits multi).map (·.bytes) = .error .schemaMismatch
#guard (convert db 1 schema {} {limits with maxFileBytes := 11} multi).map (·.bytes) =
  .error (.writeParquet (.parquet .fileLimit))

#print axioms convert_read_error
#print axioms convert_readback
#print axioms FlatInt32Writer.FromCsv.convertRows_written
#print axioms FlatInt32Writer.FromCsv.writerInput_rows

end Silmaril.Formats.Csv.ParquetIpc.FromIpc
