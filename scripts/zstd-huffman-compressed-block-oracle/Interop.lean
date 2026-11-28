module

import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Defs
meta import Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Defs

open Silmaril.Formats.Compression.Zstd
open CompressedBlock (Limits)

-- Decode only the supplied compressed bodies; the reference supplies frame extents.

private def checked {α ε : Type} [Repr ε] (stage : String) : Except ε α → IO α
  | .ok result => pure result
  | .error reason => throw (IO.userError (stage ++ ": " ++ reprStr reason))

private def expectError {α : Type} (label : String) (expected : CompressedBlock.Huffman.Error) :
    Except CompressedBlock.Huffman.Error α → IO Unit
  | .error reason => unless reason == expected do
      throw (IO.userError s!"{label}: expected {reprStr expected}, got {reprStr reason}")
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")

private def profile : Huffman.TreeDescription.Limits := ⟨128, ⟨256, 11⟩⟩

public def main (args : List String) : IO UInt32 := do
  let [window, firstPath, secondPath, out] := args | return 2
  let some w := window.toNat? | return 2
  let firstBody := (← IO.FS.readBinFile firstPath).data.toList
  let secondBody := (← IO.FS.readBinFile secondPath).data.toList
  let initial := CompressedBlock.Huffman.State.initial profile
  let limits : Limits := ⟨w, firstBody.length, 131072, 27037⟩

  let corrupt := firstBody.dropLast ++ [0]
  expectError "new tree followed by a zero sequence marker" (.block (.sequences .badEndMarker))
    (CompressedBlock.Huffman.decode limits initial firstBody.length corrupt)
  expectError "failed block yields no table to a treeless block" (.literals .unavailableTable)
    (CompressedBlock.Huffman.decode limits initial secondBody.length secondBody)
  expectError "declared body too short" (.block .sizeMismatch)
    (CompressedBlock.Huffman.decode limits initial (firstBody.length - 1) firstBody)
  expectError "truncated body" (.block .sizeMismatch)
    (CompressedBlock.Huffman.decode limits initial firstBody.length firstBody.dropLast)
  expectError "one-less input cap" (.block .inputLimit)
    (CompressedBlock.Huffman.decode {limits with inputBytes := firstBody.length - 1} initial firstBody.length firstBody)
  expectError "one-less command cap" (.block (.tables (.prefix .sequenceLimit)))
    (CompressedBlock.Huffman.decode {limits with commands := 27036} initial firstBody.length firstBody)
  let first ← checked "retry original first block" (CompressedBlock.Huffman.decode limits initial firstBody.length firstBody)

  let nextLimits : Limits := ⟨w, secondBody.length, 4096, 777⟩
  expectError "one-less output cap" (.block (.execution .outputLimit))
    (CompressedBlock.Huffman.decode {nextLimits with outputBytes := 4095} first.next secondBody.length secondBody)
  let second ← checked "retry second block with accepted history and tables"
    (CompressedBlock.Huffman.decode nextLimits first.next secondBody.length secondBody)
  for (index, bytes) in [(1, first.bytes), (2, second.bytes)] do
    IO.FS.writeBinFile (System.FilePath.mk out / s!"block-{index}.lean.bin") ⟨bytes.toArray⟩
  IO.println "Typed extent, input/command/output caps, bad marker, missing table and retry controls passed"
  return 0
