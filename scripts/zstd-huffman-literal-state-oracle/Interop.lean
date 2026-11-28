module

import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Defs
meta import Silmaril.Formats.Compression.Zstd.Huffman.LiteralState.Defs

open Silmaril.Formats.Compression.Zstd.Huffman
open LiteralState

private def profile : TreeDescription.Limits := ⟨128, ⟨256, 11⟩⟩

private def readBounded (inputCap outputCap : Nat) (prior : State profile) (bytes : List UInt8) :
    Except Error (Result profile) :=
  read ⟨inputCap, outputCap, profile⟩ prior bytes

private def checked (inputCap outputCap : Nat) (prior : State profile) (bytes : List UInt8) :
    IO (Result profile) :=
  match readBounded inputCap outputCap prior bytes with
  | .ok result => pure result
  | .error reason => throw (IO.userError (reprStr reason))

private def expectError (inputCap outputCap : Nat) (prior : State profile) (bytes : List UInt8)
    (expected : Error) : IO Unit := do
  match readBounded inputCap outputCap prior bytes with
  | .ok _ => throw (IO.userError "accepted an invalid control")
  | .error reason => unless reason == expected do throw (IO.userError (reprStr reason))

private def save (root : System.FilePath) (name : String) (result : Result profile) : IO Unit := do
  IO.FS.writeBinFile (root / (name ++ ".literals")) ⟨result.literals.expand.toArray⟩
  IO.FS.writeBinFile (root / (name ++ ".suffix")) ⟨result.rest.toArray⟩
  IO.println s!"{result.consumed} {result.literals.size}"

public def main (args : List String) : IO UInt32 := do
  let [firstPath, secondPath, root, firstBytes, firstSize, secondBytes, secondSize] := args | return 2
  let [some f, some m, some s, some n] := [firstBytes, firstSize, secondBytes, secondSize].map String.toNat?
    | return 2
  let first := (← IO.FS.readBinFile firstPath).data.toList
  let second := (← IO.FS.readBinFile secondPath).data.toList
  let empty := State.empty profile
  let installed ← checked f m empty first
  unless installed.next.table.isSome do return 4
  let reused ← checked s n installed.next second
  unless reused.next.table == installed.next.table do return 4
  save root "new-tree" installed
  save root "treeless" reused
  expectError s n empty second .unavailableTable
  expectError (f - 1) m empty first (.compressed .inputLimit)
  expectError f (m - 1) empty first (.compressed .outputLimit)
  expectError (s - 1) n installed.next second (.compressed .inputLimit)
  expectError s (n - 1) installed.next second (.compressed .outputLimit)

  let raw ← checked 2 1 installed.next [8, 97, 0]
  let rle ← checked 2 3 raw.next [25, 98, 0]
  unless raw.literals == .raw [97] && rle.literals == .rle 3 98 &&
      raw.consumed == 2 && rle.consumed == 2 && raw.rest == [0] && rle.rest == [0] &&
      raw.next.table == installed.next.table && rle.next.table == installed.next.table do return 4
  let interposed ← checked s n rle.next second
  unless interposed.next.table == reused.next.table do return 4
  save root "interposed" interposed
  return 0
