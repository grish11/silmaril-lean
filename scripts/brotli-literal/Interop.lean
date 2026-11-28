module

import Lean
import Silmaril.Formats.Compression.Brotli.Literal.Defs
meta import Silmaril.Formats.Compression.Brotli.Literal.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def take (reader : LSBReader) (width : Nat) : IO (Nat × LSBReader) :=
  match reader.readBits width with
  | none => throw (IO.userError "fixture framing truncated")
  | some result => pure result

-- Locate the first compressed header and MLEN from the fixture itself.
private def framing (before : LSBReader) : IO (Nat × LSBReader) := do
  let (window, cursor) ← take before 1
  let cursor ← if window = 0 then pure cursor else do
    let (short, cursor) ← take cursor 3
    if short ≠ 0 then pure cursor else do
      let (long, cursor) ← take cursor 3
      if long = 1 then throw (IO.userError "reserved window")
      pure cursor
  let (last, cursor) ← take cursor 1
  let cursor ← if last = 0 then pure cursor else do
    let (empty, cursor) ← take cursor 1
    if empty ≠ 0 then throw (IO.userError "empty first block")
    pure cursor
  let (selector, cursor) ← take cursor 2
  if selector = 3 then throw (IO.userError "metadata first block")
  let width := 4 * (4 + selector)
  let (sizeMinusOne, cursor) ← take cursor width
  if selector ≠ 0 && sizeMinusOne < 2 ^ (width - 4) then
    throw (IO.userError "noncanonical fixture length")
  if last ≠ 0 then pure (sizeMinusOne + 1, cursor)
  else
    let (raw, cursor) ← take cursor 1
    if raw ≠ 0 then throw (IO.userError "uncompressed first block")
    pure (sizeMinusOne + 1, cursor)

private def checkContexts (path : String) : IO UInt32 := do
  let mut bytes := ByteArray.empty
  for mode in [ContextHeader.Mode.lsb6, .msb6, .utf8, .signed] do
    for first in [:256] do
      for second in [:256] do
        let context := Literal.contextId mode ⟨UInt8.ofNat first, UInt8.ofNat second⟩
        bytes := bytes.push (UInt8.ofNat context.val)
  IO.FS.writeBinFile path bytes
  return 0

private def sameCursor (a b : LSBReader) : Bool :=
  a.totalRead == b.totalRead && a.count == b.count && a.buffer == b.buffer && a.input == b.input

private def checkInsertion (path : String) : IO UInt32 := do
  let stream := LSBReader.ofByteArray (← IO.FS.readBinFile path)
  let (length, preamble) ← framing stream
  let (header, payload) ← requireIO (CompressedHeader.read ⟨17408, 768, 100000⟩ preamble)
  let (command, before) ← requireIO (Command.readSingle header 63 payload)
  let decode := fun (limits : Literal.Limits) =>
    Literal.read header command length limits Literal.State.start before
  let (result, after) ← requireIO (decode ⟨length, 15 * command.insertLength⟩)
  let cap := after.totalRead - before.totalRead
  let (exact, checked) ← requireIO (decode ⟨result.bytes.length, cap⟩)
  unless result == exact && sameCursor after checked do
    throw (IO.userError "exact-limit insertion differs")
  if cap > 0 then
    match decode ⟨length, cap - 1⟩ with
    | .error (.symbol .bitLimit) => pure ()
    | _ => throw (IO.userError "one-bit-short cap did not fail as expected")
  if result.bytes.length > 0 then
    match decode ⟨result.bytes.length - 1, cap⟩ with
    | .error .outputLimit => pure ()
    | _ => throw (IO.userError "one-byte-short cap did not fail as expected")
  let (_, expected) ← take stream after.totalRead
  unless sameCursor after expected do throw (IO.userError "insertion suffix differs")

  let tables ← requireIO (Literal.source header)
  let mut history := Literal.History.start
  let mut pos := before.totalRead
  let mut steps : Array (List Nat) := #[]
  for byte in result.bytes do
    let some tree := tables.treeIndex? history | throw (IO.userError "fixture context selection")
    let some table := tables.trees[tree]? | throw (IO.userError "fixture literal tree")
    let some (_, width) := table.codeFor byte.toNat | throw (IO.userError "fixture literal code")
    let ctx := Literal.contextId tables.mode history
    steps := steps.push [history.mostRecent.toNat, history.secondRecent.toNat, ctx.val,
      tree, byte.toNat, pos, pos + width]
    history := history.push byte
    pos := pos + width
  unless pos == after.totalRead && history == result.state.history do
    throw (IO.userError "fixture history or code extent differs")

  IO.println (Json.mkObj [
    ("start", toJson preamble.totalRead),
    ("payload", toJson payload.totalRead),
    ("meta_length", toJson length),
    ("mode", toJson tables.mode.code),
    ("trees", toJson tables.trees.length),
    ("command", toJson [command.symbol.val, command.insertLength, command.copyLength,
      if command.distance == .implicitZero then 0 else 1]),
    ("begin", toJson before.totalRead),
    ("end", toJson after.totalRead),
    ("bytes", toJson (result.bytes.map UInt8.toNat)),
    ("history", toJson [history.mostRecent.toNat, history.secondRecent.toNat]),
    ("done", toJson (result.next == .endOfMetaBlock)),
    ("steps", toJson steps)]).compress
  return 0

public def main (args : List String) : IO UInt32 :=
  match args with
  | ["--contexts", path] => checkContexts path
  | [path] => checkInsertion path
  | _ => pure 2
