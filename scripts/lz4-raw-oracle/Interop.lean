module

import Silmaril.Formats.Compression.Lz4Raw.Defs
meta import Silmaril.Formats.Compression.Lz4Raw.Defs

open Silmaril.Formats.Compression.Lz4Raw

private def sizeArg (text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError "expected a size")

public def main (args : List String) : IO UInt32 := do
  let mode :: source :: target :: sizes := args
    | throw (IO.userError "usage: Interop.lean encode|decode INPUT OUTPUT [C CLIMIT U ULIMIT]")
  let bytes := (← IO.FS.readBinFile source).data.toList
  match mode, sizes with
  | "encode", [] =>
    IO.FS.writeBinFile target ⟨(encodeLiteral bytes).toArray⟩
    return 0
  | "decode", [compressed, compressedLimit, expected, outputLimit] =>
    let bounds := ⟨← sizeArg compressed, ← sizeArg compressedLimit, ← sizeArg expected, ← sizeArg outputLimit⟩
    match decode bounds bytes with
    | .ok out =>
      IO.FS.writeBinFile target ⟨out.toArray⟩
      return 0
    | .error error =>
      IO.println (reprStr error)
      return 3
  | _, _ => throw (IO.userError "invalid mode or sizes")
