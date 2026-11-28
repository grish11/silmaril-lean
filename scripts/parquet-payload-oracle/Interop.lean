module

import Silmaril.Formats.Parquet.Payload.Defs
meta import Silmaril.Formats.Parquet.Payload.Defs

open Silmaril.Formats.Parquet.Payload

private def sizeArg (text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError "expected an unsigned size")

private def label : Error → String
  | .compressedLimit => "compressedLimit"
  | .outputLimit => "outputLimit"
  | .compressedSizeMismatch => "compressedSizeMismatch"
  | .outputSizeMismatch => "outputSizeMismatch"
  | .unsupportedCodec id => s!"unsupportedCodec {id}"
  | .malformed codec => s!"malformed {codec.id}"
  | .trailingInput codec => s!"trailingInput {codec.id}"
  | .gzipIncomplete => "gzipIncomplete"

public def main (args : List String) : IO UInt32 := do
  let [source, target, id, csize, climit, usize, ulimit, gzipCalls] := args
    | throw (IO.userError "usage: Interop.lean SOURCE TARGET CODEC CSIZE CLIMIT USIZE ULIMIT CALLS")
  let some id := id.toInt? | throw (IO.userError "expected a signed codec ID")
  let bounds := ⟨← sizeArg csize, ← sizeArg climit, ← sizeArg usize, ← sizeArg ulimit, ← sizeArg gzipCalls⟩
  let input := (← IO.FS.readBinFile source).data.toList
  match decode bounds id input with
  | .ok out => IO.FS.writeBinFile target ⟨out.toArray⟩; return 0
  | .error error => IO.println (label error); return 3
