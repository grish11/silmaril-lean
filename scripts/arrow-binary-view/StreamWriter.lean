module

import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Examples
meta import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Examples

open Silmaril Silmaril.Formats.Arrow.BinaryView
open StreamWriter StreamWriter.Examples

private def write (directory : System.FilePath) (name : String) (field : Schema.Field)
    (batches : List (Schema.Values field.kind)) : IO Unit := do
  match emit {} {} field batches with
  | .error failure => throw (IO.userError s!"{name}: {repr failure}")
  | .ok bytes => IO.FS.writeBinFile (directory / (name ++ ".arrow")) bytes.toByteArray

public def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: StreamWriter.lean DIR")
  IO.FS.createDirAll directory
  for (fixture, name, nullable, batches) in binaryCases do
    write directory fixture ⟨name, nullable, .binary⟩ batches
  write directory "utf8" utf8Field utf8Batches
