module

import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs
meta import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.MixedV1Writer.Multi

private def raw : Bytes := .ofList [255, 0, 128]
private def long : Bytes := .ofList (List.replicate 20 42)

private def required : Input :=
  ⟨⟨"id", .required⟩, ⟨"raw", .required⟩,
    [⟨.required [-2147483648, 0], .required [raw, .empty]⟩,
     ⟨.required [2147483647], .required [long]⟩]⟩

private def middle : Input :=
  ⟨⟨"count", .optional⟩, ⟨"clé", .optional⟩,
    [⟨.optional [some (-7)], .optional [none]⟩,
     ⟨.optional [], .optional []⟩,
     ⟨.optional [none, some 0], .optional [some .empty, some raw]⟩]⟩

private def manyGroup (i : Nat) : Group :=
  if i = 7 then ⟨.required [], .optional []⟩
  else ⟨.required [Int32.ofInt (Int.ofNat i - 8)],
    .optional [if i % 3 = 0 then none else some (.ofList [UInt8.ofNat i, 0, 255])]⟩

private def many : Input :=
  ⟨⟨"ordinal", .required⟩, ⟨"payload", .optional⟩, (List.range 16).map manyGroup⟩

private def limits : Limits :=
  ⟨⟨8192, {}, ⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩,
    ⟨⟨{}, 32, ⟨128, 128, ⟨16, 32⟩, 0⟩⟩, ⟨128, 20⟩⟩, {}⟩, 16, 16⟩

private def reject (caps : Limits) (input : Input) (expected : Error) : IO Unit := do
  let .error actual := emit caps input
    | throw (IO.userError s!"expected {repr expected}, got a file")
  unless actual == expected do
    throw (IO.userError s!"expected {repr expected}, got {repr actual}")

private def write (directory : System.FilePath) (name : String) (input : Input)
    (order : MixedV1Writer.Order := .intFirst) : IO Unit := do
  let writeFile := match order with | .intFirst => emit | .byteFirst => emitOrdered .byteFirst
  let .ok output := writeFile limits input | throw (IO.userError s!"{name}: emission failed")
  let .ok checked := Int32ByteArrayGroup.openFile limits.writer.readback output.bytes
      input.intField input.byteField
    | throw (IO.userError s!"{name}: mixed open failed")
  let (intOrdinal, byteOrdinal) := order.arrange 0 1
  unless checked.int32Binding.columnOrdinal == intOrdinal && checked.byteArrayBinding.columnOrdinal == byteOrdinal do
    throw (IO.userError s!"{name}: wrong physical column ordinals")
  unless checked.snapshot.groupCount == input.groups.length do
    throw (IO.userError s!"{name}: wrong actual footer group count")
  for (group, ordinal) in input.groups.zipIdx do
    let .ok read := checked.readGroup limits.writer.readback ordinal
      | throw (IO.userError s!"{name}: cannot read group {ordinal}")
    unless read == group.rows do throw (IO.userError s!"{name}: wrong pairs at group {ordinal}")
  let .error (.int32 (.groupIndex actual)) := checked.readGroup limits.writer.readback input.groups.length
    | throw (IO.userError s!"{name}: EOF ordinal admitted a group")
  unless actual == input.groups.length do throw (IO.userError s!"{name}: wrong failed ordinal")
  let writer := { limits.writer with maxFileBytes := output.bytes.length }
  let exactCaps := ⟨writer, input.groups.length, input.totalRows⟩
  let .ok bounded := writeFile exactCaps input | throw (IO.userError s!"{name}: exact caps refused")
  unless bounded.bytes == output.bytes do throw (IO.userError s!"{name}: caps changed the wire")
  IO.FS.writeBinFile (directory / s!"{name}.parquet") output.bytes.data

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected an output directory")
  let directory := System.FilePath.mk path
  IO.FS.createDirAll directory
  write directory "required" required
  write directory "empty-middle" middle
  write directory "long-group-list" many
  write directory "byte-first" middle .byteFirst

  let group : Group :=
    ⟨.required [-2147483648, 0, 17, 2147483647, -1],
      .optional [none, some .empty, some raw, none, some long]⟩
  let singleton := { many with groups := [group] }
  let .ok previous := MixedV1Writer.emit limits.writer (singleton.single group)
    | throw (IO.userError "single-group writer failed")
  let .ok current := emit limits singleton | throw (IO.userError "singleton plan failed")
  unless current.bytes == previous.bytes do throw (IO.userError "singleton framing changed")
  IO.FS.writeBinFile (directory / "singleton.parquet") current.bytes.data

  reject limits { middle with groups := [] } .groupLimit
  reject { limits with maxGroups := 2 } middle .groupLimit
  reject { limits with maxTotalRows := 2 } middle .totalRows
  reject { limits with writer := { limits.writer with maxFileBytes := 12 } } middle .fileLimit
  reject { limits with writer := { limits.writer with footer := { limits.writer.footer with maxFooterBytes := 0 } } }
    middle (.footer .byteLimit)
  reject limits { middle with intField := ⟨"count", .required⟩ } .schemaOrCount
  reject limits { middle with groups := [⟨.optional [], .optional [none]⟩] } .schemaOrCount
  let readback := limits.writer.readback
  let restricted := { readback with column := { readback.column with maxRows := 1 } }
  reject { limits with writer := { limits.writer with readback := restricted } }
    middle (.groupReadback 2 (.int32 (.column 2 0 "count" (.rowLimit 1 2))))
  IO.println "Four multi-group files, a byte-identical singleton, exact caps and eight typed refusals."
