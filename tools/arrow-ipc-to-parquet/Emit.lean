module

import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Defs
meta import Silmaril.Formats.Csv.ParquetIpc.FromIpc.Defs

open Silmaril Silmaril.Relational Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Csv.ParquetIpc.FromIpc
open Silmaril.Formats.Relational.NamedTable (Packed)
open Silmaril.Formats.Parquet.Snapshot.FlatInt32 (Cell)

private def schema : Scan.Schema String Unit := ⟨2, fun i => (if i.val = 0 then "café" else "値", ())⟩
private def db : Packed Nat Csv.Field Cell := fun _ => none
private def limits : FlatInt32Writer.Limits := ⟨8, 16384, {}, ⟨{}, 64, ⟨4096, 4096, ⟨64, 512⟩, 0⟩⟩⟩

public def main (args : List String) : IO Unit := do
  let [source, target] := args
    | throw (IO.userError "usage: Emit.lean INPUT.arrows OUTPUT.parquet")
  let bytes ← IO.FS.readBinFile source
  let input := KBytes.ofChunks 1 bytes.size (bytes.data.toList.map UInt8.toNat)
  let .ok result := convert db 1 schema {} limits input
    | throw (IO.userError "checked IPC to Parquet conversion failed")
  IO.FS.writeBinFile target result.bytes.data
