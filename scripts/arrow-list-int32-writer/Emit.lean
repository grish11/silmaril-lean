module

import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Defs
meta import Silmaril.Formats.Arrow.ListInt32.Stream.Writer.Defs

open Silmaril.Formats.Arrow.ListInt32

private def batches : List (List Stream.Row) :=
  [[none, some [], some [none], some [some (-7), none, some 0]], [],
    [some [some (-2147483648), some 2147483647], none, some []], [none, none]]

public def main (args : List String) : IO Unit := do
  let [path, schemaOnlyPath] := args
    | throw (IO.userError "usage: Emit.lean STREAM SCHEMA_ONLY_STREAM")
  let field : Field := ⟨"résultats", "élément"⟩
  let .ok wire := Stream.Writer.emit {} field batches
    | throw (IO.userError "native LIST stream emission failed")
  let .ok schemaOnly := Stream.Writer.emit {} field []
    | throw (IO.userError "native LIST schema-only emission failed")
  IO.FS.writeBinFile path wire.toByteArray
  IO.FS.writeBinFile schemaOnlyPath schemaOnly.toByteArray
