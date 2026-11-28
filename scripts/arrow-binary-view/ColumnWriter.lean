module

import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Examples
meta import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Examples

open Silmaril Silmaril.Formats.Arrow.BinaryView.Column.Writer

private def write (root : System.FilePath) (name : String) (result : Except Error Emitted) : IO Unit := do
  let .ok emitted := result | throw (IO.userError s!"failed to emit fixture {name}")
  let path := root / name
  IO.FS.createDirAll path
  let buffers := emitted.buffers
  let count := buffers.payload.data.size
  IO.FS.writeFile (path / "node.txt") s!"{emitted.node.length} {emitted.node.nullCount} {count}\n"
  IO.FS.writeBinFile (path / "validity.bin") buffers.validity.toByteArray
  IO.FS.writeBinFile (path / "views.bin") buffers.payload.views.toByteArray
  for index in [:count] do
    IO.FS.writeBinFile (path / s!"data-{index}.bin") buffers.payload.data[index]!.toByteArray

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: ColumnWriter.lean DIR")
  for (name, values) in binaryCases do
    write directory name (emitBinary {} true values)
  for (name, values) in utf8Cases do
    write directory name (emitUtf8 {} true values)
