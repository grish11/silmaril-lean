module

public import Silmaril.Wasm.Region.ByteMap.Produce.Defs
public import Lean.Data.Json

/-! Native coverage measurements. Successful checks execute the certified API,
but these JSON measurements are not per-file kernel theorem declarations. -/

@[expose] public section
open Lean Silmaril.Wasm.Region Silmaril.Wasm.Region.ByteMap

def reportFile (path : String) : IO Json := do
  let bytes ← IO.FS.readBinFile path
  let raw := bytes.toList
  let some decoded := Silmaril.Wasm.Binary.Core.decode? bytes
    | return Json.mkObj [("file", toJson path), ("status", toJson "module-decode-rejected")]
  let some layout := Produce.layout? raw decoded
    | return Json.mkObj [("file", toJson path), ("status", toJson "no-code-layout"),
        ("definedBodies", toJson decoded.funcs.length)]
  let some source := ModuleSource.validate? raw layout
    | return Json.mkObj [("file", toJson path), ("status", toJson "source-check-rejected")]
  let mut rows : Array Json := #[]
  let mut expected := 0
  let mut mapped := 0
  let mut complete := 0
  for i in List.finRange source.layout.bodies.length do
    let input := (source.layout.bodies[i]).input
    let count := (Nested.inventory input).eraseDups.length
    expected := expected + count
    let result := Produce.fullMap? input
    let number := result.map (fun r => r.certified.map.entries.length) |>.getD 0
    if result.isSome then complete := complete + 1
    mapped := mapped + number
    rows := rows.push <| Json.mkObj [
      ("localIndex", toJson i.val), ("functionIndex", toJson input.functionIndex),
      ("moduleBodyOffset", toJson (source.layout.bodyStart i.val)),
      ("bodyBytes", toJson input.bytes.length), ("distinctInventoryPositions", toJson count),
      ("mappedPositions", toJson number), ("complete", toJson result.isSome)]
  return Json.mkObj [
    ("file", toJson path), ("status", toJson "source-checked"), ("bytes", toJson raw.length),
    ("importedFunctions", toJson source.decoded.importedFunctions.length),
    ("definedBodies", toJson source.layout.bodies.length), ("completeBodies", toJson complete),
    ("distinctInventoryPositions", toJson expected), ("mappedPositions", toJson mapped),
    ("bodies", Json.arr rows)]

def main (args : List String) : IO Unit := do
  let rows ← args.mapM reportFile
  (← IO.getStdout).putStrLn (Json.arr rows.toArray).pretty
