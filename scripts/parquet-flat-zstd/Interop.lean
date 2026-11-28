module

import Lean
import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs
meta import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs

open Lean
open Silmaril.Formats
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.FlatColumn

private def result (read : Except (FlatColumn.Error Zstd.Error) (List (Option Int32))) : Json :=
  match read with
  | .ok slots => Json.mkObj [("slots", toJson (slots.map (·.map Int32.toInt)))]
  | .error (.groupIndex group) => Json.mkObj [("groupError", toJson group)]
  | .error (.column group column name reason) =>
    Json.mkObj [("columnError", toJson [group, column]), ("name", toJson name), ("reason", toJson (reprStr reason))]
  | .error (.page group column name index offset reason) =>
    Json.mkObj [("pageError", toJson [group, column, index, offset]), ("name", toJson name),
      ("reason", toJson (reprStr reason))]

private def requireIO {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

public def main (args : List String) : IO UInt32 := do
  let [file, instructions] := args | return 2
  let source : Bytes := ⟨← IO.FS.readBinFile file⟩
  let snapshot ← requireIO (Snapshot.check (Failure := Unit) {} source)
  for line in (← IO.FS.readFile instructions).splitOn "\n" do
    if line.isEmpty then continue
    let [name, nullable, groupArg, inputArg, outputArg, windowArg, commandsArg] := line.splitOn " " | return 2
    let (some group, some inputCap, some outputCap, some window, some commands) :=
      (groupArg.toNat?, inputArg.toNat?, outputArg.toNat?, windowArg.toNat?, commandsArg.toNat?) | return 2
    let layout : FlatColumn.Layout := if nullable == "optional" then .optional else .required
    let binding ← requireIO (bindColumn snapshot ⟨name, .int32, layout⟩)
    let limits : Zstd.Limits := ⟨{}, ⟨inputCap, outputCap, ⟨262144, 1048576⟩, 0⟩, ⟨window, commands⟩⟩
    IO.println (result (Zstd.readColumn binding limits group)).compress
  return 0
