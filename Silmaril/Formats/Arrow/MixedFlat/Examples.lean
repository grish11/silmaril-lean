module

import Silmaril.Formats.Arrow.MixedFlat.Defs
meta import Silmaril.Formats.Arrow.MixedFlat.Defs
import Silmaril.Formats.Arrow.MixedFlat.Fixture
meta import Silmaril.Formats.Arrow.MixedFlat.Fixture

open Silmaril Silmaril.Formats
open Arrow.MixedFlat Arrow.MixedFlat.Fixture

private inductive Values where
  | primitive (values : Arrow.Column)
  | binary (values : List (Option (List UInt8)))
  | text (values : List (Option String))
  deriving DecidableEq

private def observe : Column → Values
  | .primitive values => .primitive values
  | .binaryView values => .binary (values.map (·.map KBytes.toList))
  | .utf8View values => .text values

private def valuesOf (result : Observed) : Nat × List (Field × Values) :=
  (result.rowCount, result.columns.map fun (field, column) => (field, observe column))

private def intField : Field := ⟨"i", true, .primitive .int32⟩
private def binaryField : Field := ⟨"b", true, .view .binary⟩
private def utf8Field : Field := ⟨"u", true, .primitive .utf8⟩
private def viewField : Field := ⟨"v", true, .view .utf8⟩

private def ints : Values := .primitive [some (.int32 1), none, some (.int32 (-7)), some (.int32 0)]
private def binary : Values := .binary [some (List.replicate 13 120), none, some [],
  some (List.replicate 17 121)]
private def utf8 : Values := .primitive [some (.utf8 "α"), some (.utf8 ""), none, some (.utf8 "last")]
private def view : Values := .text [none, some "", some "short", some "雪雪雪雪雪雪"]

#guard ((readBatch {} mixedSchema mixedRecord mixedBody).map valuesOf).toOption =
  some (4, [(intField, ints), (binaryField, binary), (utf8Field, utf8), (viewField, view)])
#guard ((readBatch {} reorderedSchema reorderedRecord reorderedBody).map valuesOf).toOption =
  some (4, [(viewField, view), (utf8Field, utf8), (binaryField, binary), (intField, ints)])
#guard ((readBatch {} emptySchema emptyRecord emptyBody).map valuesOf).toOption =
  some (0, [(intField, .primitive []), (binaryField, .binary []), (utf8Field, .primitive []),
    (viewField, .text [])])

private def shape (schema record body : KBytes) : Option (List (Option Nat × Nat)) := do
  let fields ← (readSchema {} schema).toOption
  let metadata ← (readMetadata {} 8 16 fields record).toOption
  let plan ← (bindBatch {} fields metadata body).toOption
  return plan.assignment.groups.map fun group => (group.count, group.buffers.length)

#guard shape mixedSchema mixedRecord mixedBody = some [(none, 2), (some 2, 4), (none, 3), (some 1, 3)]
#guard shape reorderedSchema reorderedRecord reorderedBody = some [(some 1, 3), (none, 3), (some 2, 4), (none, 2)]
#guard shape emptySchema emptyRecord emptyBody = some [(none, 2), (some 0, 2), (none, 3), (some 0, 2)]

private def patch (bytes : KBytes) (start width value : Nat) : KBytes :=
  bytes.slice 0 start ++ .leaf width value ++
    bytes.slice (start + width) (bytes.len - (start + width))

private def rejects (metadata : KBytes) (expected : Error) (limits : Limits := {}) : Bool :=
  match readBatch limits mixedSchema metadata mixedBody with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard rejects (patch mixedRecord mixedCountSlot 2 0) (.metadata (.countCardinality 2 0))
#guard rejects (patch mixedRecord mixedCountVector 4 1) (.metadata (.countCardinality 2 1))
#guard rejects (patch mixedRecord mixedCountVector 4 3) (.metadata (.countCardinality 2 3))
#guard rejects (patch mixedRecord mixedCountWord 8 (2^63)) (.metadata (.negativeCount 0))
#guard rejects mixedRecord (.metadata (.dataBufferLimit 0)) { view := { dataBuffers := 1 } }
#guard rejects mixedRecord (.metadata .totalDataBufferLimit) { totalDataBuffers := 2 }
#guard rejects (patch mixedRecord mixedDescriptorVector 4 11) (.metadata (.descriptorCount 12 11))
#guard rejects (patch mixedRecord mixedThirdNode 8 3) (.plan (.field 2 .invalidNode))
#guard rejects (patch mixedRecord mixedBinaryValidity 8 0) (.body (.malformed .batchLayout))
#guard rejects (patch (patch mixedRecord mixedCountWord 8 1) (mixedCountWord + 8) 8 2)
  (.field 1 (.view (.slot 3 .invalidReference)))
#guard rejects mixedRecord (.body (.limit .totalCells)) { observation := { totalCells := 15 } }

private def zeroNode : Arrow.FieldNode := ⟨0, 0⟩
private def zeroBuffer : Arrow.Buffer := ⟨0, 0⟩

#guard match assign 0 [intField, binaryField] [zeroNode] [] [] 0 with
  | .error (.field 0 (.missingDescriptors 2 0)) => true
  | _ => false
#guard match assign 0 [intField, binaryField] [zeroNode] [] [zeroBuffer, zeroBuffer] 0 with
  | .error (.field 1 .missingNode) => true
  | _ => false
#guard match assign 0 [intField, binaryField] [zeroNode, zeroNode] [] [zeroBuffer, zeroBuffer] 0 with
  | .error (.field 1 .missingCount) => true
  | _ => false
#guard match assign 0 [intField] [zeroNode] [0] [zeroBuffer, zeroBuffer] 0 with
  | .error (.excess 0 1 0) => true
  | _ => false
#guard match assign 0 [intField] [zeroNode, zeroNode] [] [zeroBuffer, zeroBuffer, zeroBuffer] 0 with
  | .error (.excess 1 0 1) => true
  | _ => false

#guard match assign 1 [{ intField with nullable := false }] [⟨1, 1⟩] [] [zeroBuffer, zeroBuffer] 0 with
  | .error (.field 0 .invalidNode) => true
  | _ => false

#guard match Arrow.readMessage {} mixedSchema, Arrow.SchemaReader.readMessage {} mixedSchema with
  | .error (.unsupported (.fieldType 23)), .error (.unsupported (.fieldType 23)) => true
  | _, _ => false
