module

import Silmaril.Formats.Compression.Zstd.RleSequences.Defs
meta import Silmaril.Formats.Compression.Zstd.RleSequences.Defs

open Silmaril.Formats.Compression.Zstd

/-- Test-only composition of literal parsing, wire decoding and execution. -/
public def main (args : List String) : IO UInt32 := do
  let [source, prior, target, commandCap] := args
    | throw (IO.userError "usage: RleInterop.lean BODY HISTORY OUTPUT COMMAND_CAP")
  let some commandCap := commandCap.toNat? | throw (IO.userError "invalid command cap")
  let body := (← IO.FS.readBinFile source).data.toList
  let history := (← IO.FS.readBinFile prior).data
  let (literals, sequenceBytes) ← match LiteralBlock.parseLiterals 1024 body with
    | .ok parsed => pure parsed
    | .error error => throw (IO.userError (reprStr error))
  match RleSequences.decode ⟨131072, commandCap⟩ sequenceBytes with
  | .error error =>
    IO.println (reprStr error)
    return 3
  | .ok commands =>
    match Sequence.execute ⟨1024, 1024⟩ history literals.expand Sequence.RepeatOffsets.initial commands with
    | .error error => throw (IO.userError (reprStr error))
    | .ok result =>
      IO.FS.writeBinFile target ⟨result.bytes.toArray⟩
      for command in commands do
        IO.println s!"{command.literalLength} {command.offsetValue} {command.matchLength}"
      return 0
