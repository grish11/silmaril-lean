module

import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Defs
meta import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Defs

open Silmaril.Formats.Hive.PartitionPath

private def emit (keys : List String) (encoding : Positional.Encoding)
    (entries : Partition) (suffix : String) : IO Unit :=
  match Filename.render 128 keys encoding {} entries suffix with
  | .ok leaf => IO.println leaf
  | .error error => throw (IO.userError (reprStr error))

public def main : IO Unit := do
  emit ["region", "year"] .uri [("region", some "a_b"), ("year", some "7")] "part-0.parquet"
  emit ["region", "year"] .uri [("region", some "café/x%5F"), ("year", some "8")] "part-1.parquet"
  emit ["region", "year"] .literal [("region", some "café%5f"), ("year", some "7")] "part-2.parquet"
  emit [] .uri [] "part-3.parquet"
