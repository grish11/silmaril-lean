module

import Silmaril.Formats.Compression.Zstd.Sequence.Defs
meta import Silmaril.Formats.Compression.Zstd.Sequence.Defs

open Silmaril.Formats.Compression.Zstd.Sequence

private def numbers (text : String) : IO (List Nat) :=
  (text.splitOn " ").filter (· ≠ "") |>.mapM fun word =>
    match word.toNat? with
    | some n => pure n
    | none => throw (IO.userError "invalid fixture number")

private def commands : List Nat → IO (List Command)
  | [] => pure []
  | literals :: offset :: length :: rest => do
    return ⟨literals, offset, length⟩ :: (← commands rest)
  | _ => throw (IO.userError "incomplete fixture command")

/-- Fixture driver. A row contains triples on the left and bytes on the right.
    An empty left section supplies a raw history block. -/
public def main (args : List String) : IO UInt32 := do
  let [source, target, window, capacity] := args
    | throw (IO.userError "usage: SequenceInterop.lean FIXTURE OUTPUT WINDOW OUTPUT_LIMIT")
  let some window := window.toNat? | throw (IO.userError "invalid window")
  let some capacity := capacity.toNat? | throw (IO.userError "invalid output limit")
  let mut output : Array UInt8 := #[]
  let mut offsets := RepeatOffsets.initial
  for row in (← IO.FS.readFile source).splitOn "\n" do
    if row.isEmpty then continue
    let [triples, bytes] := row.splitOn "|" | throw (IO.userError "invalid fixture row")
    let literals := (← numbers bytes).map Nat.toUInt8
    let cmds ← commands (← numbers triples)
    if cmds.isEmpty then
      output := output ++ literals.toArray
    else
      let history := output.extract (output.size - window) output.size
      match execute ⟨window, capacity - output.size⟩ history literals offsets cmds with
      | .ok decoded =>
        output := output ++ decoded.bytes.toArray
        offsets := decoded.offsets
      | .error error =>
        IO.println (reprStr error)
        return 3
  IO.FS.writeBinFile target ⟨output⟩
  IO.println s!"{offsets.first} {offsets.second} {offsets.third}"
  return 0
