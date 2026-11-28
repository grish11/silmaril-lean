module

import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Defs
meta import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Defs

open Silmaril.Formats.Hive.PartitionPath
open Silmaril.Formats.Hive.PartitionPath.Positional

private def emit (keys : List String) (encoding : Encoding) (options : Options)
    (entries : Partition) : IO Unit :=
  match Positional.render ⟨128, 64⟩ keys encoding options entries with
  | .ok directory => IO.println directory
  | .error reason => throw (IO.userError (reprStr reason))

public def main (args : List String) : IO Unit := do
  let keys := ["region", "year"]
  let entries := fun region => [("region", some region), ("year", some "7")]
  emit keys .uri {} (entries "café/blue=%5F:west\\x")
  emit keys .literal {} (entries "café=blue%5F_west")
  emit keys .uri {nullMarker := "different"} (entries "__HIVE_DEFAULT_PARTITION__")
  emit [] .uri {} []
  if args == ["--scan"] then
    emit keys .uri {} [("region", some "apart"), ("year", some "8")]
    emit keys .uri {} (entries "zebra")
