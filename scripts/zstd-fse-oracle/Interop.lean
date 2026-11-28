module

import Silmaril.Formats.Compression.Zstd.FseTable.Defs
meta import Silmaril.Formats.Compression.Zstd.FseTable.Defs

open Silmaril.Formats.Compression.Zstd.FseTable

private def fromName : String → Option Alphabet
  | "literal" => some .literalLength
  | "offset" => some .offset
  | "match" => some .matchLength
  | _ => none

public def main (args : List String) : IO UInt32 := do
  let name :: raw := args | throw (IO.userError "usage: Interop.lean PRESET | LOG WEIGHT...")
  let limits : Limits := ⟨9, 256⟩
  let result ← match fromName name with
    | some alphabet =>
      let input := [0xaa, 0xbb]
      match selectPredefined limits alphabet 0 input with
      | .ok (table, tail) =>
        if tail ≠ input then throw (IO.userError "predefined table consumed fixture bytes")
        else pure (.ok table)
      | .error error => pure (.error error)
    | none =>
      let some log := name.toNat? | throw (IO.userError "invalid fixture log")
      let some weights := raw.mapM String.toInt? | throw (IO.userError "invalid fixture count")
      pure (build limits ⟨log, weights⟩)
  match result with
  | .error error =>
    IO.println (reprStr error)
    return 3
  | .ok table =>
    IO.println table.log
    for row in table.rows do
      IO.println s!"{row.symbol} {row.bits} {row.baseline}"
    return 0
