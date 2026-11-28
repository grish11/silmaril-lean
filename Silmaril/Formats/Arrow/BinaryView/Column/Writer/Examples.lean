module

public import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
meta import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Defs
import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Fixture

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Column.Writer

def slicedZeros : KBytes :=
  ((KBytes.leaf 8 0x42) ++ .leaf 9 0x430000000000000000).slice 1 13

def binaryInline : List (Option KBytes) := [some .empty, some (.leaf 12 (256^12 - 1))]
def utf8Inline : List (Option String) := [some "", some "éééééé"]

def binaryCases : List (String × List (Option KBytes)) :=
  [("binaryMixed", none :: binaryInline ++ [some slicedZeros, some (utf8Bytes "tailtailtailtailtailtail")]),
   ("binaryInline", binaryInline), ("binaryNulls", [none, none]), ("binaryEmpty", [])]

def utf8Cases : List (String × List (Option String)) :=
  [("utf8Mixed", none :: utf8Inline ++ [some "ééééééx", some "雪雪雪雪雪雪雪雪雪"]),
   ("utf8Inline", utf8Inline), ("utf8Nulls", [none, none]), ("utf8Empty", [])]

private def binaryObserves (fixture : FieldNode × Buffers) (values : List (Option KBytes)) : Bool :=
  match Column.readBinary {} fixture.1 true fixture.2 with
  | .error _ => false
  | .ok decoded => decoded.map (·.map KBytes.toList) == values.map (·.map KBytes.toList)

private def utf8Observes (fixture : FieldNode × Buffers) (values : List (Option String)) : Bool :=
  match Column.readUtf8 {} fixture.1 true fixture.2 with
  | .error _ => false
  | .ok decoded => decoded == values

#guard ([Fixture.binaryMixed, Fixture.binaryInline, Fixture.binaryNulls, Fixture.binaryEmpty].zip binaryCases).all
  (fun (fixture, _, values) => binaryObserves fixture values)

#guard ([Fixture.utf8Mixed, Fixture.utf8Inline, Fixture.utf8Nulls, Fixture.utf8Empty].zip utf8Cases).all
  (fun (fixture, _, values) => utf8Observes fixture values)

#guard binaryCases.all fun (_, values) =>
  match emitBinary {} true values with
  | .error _ => false
  | .ok output => output.buffers.payload.data.size == dataCount (longBytes KBytes.len values) &&
    binaryObserves (output.node, output.buffers) values

#guard utf8Cases.all fun (_, values) =>
  match emitUtf8 {} true values with
  | .error _ => false
  | .ok output => output.buffers.payload.data.size == dataCount (longBytes String.utf8ByteSize values) &&
    utf8Observes (output.node, output.buffers) values

#guard match emitBinary {} true (binaryCases.head!.2) with
  | .error _ => false
  | .ok output =>
    let bytes := output.buffers.payload.views
    output.node.length == 5 && output.node.nullCount == 1 && output.buffers.validity.read 0 1 == 30 &&
      bytes.len == 80 && bytes.read 0 16 == 0 &&
      bytes.read 32 4 == 12 && bytes.read 36 12 == 256^12 - 1 &&
      bytes.read 48 4 == 13 && bytes.read 52 4 == 0 && bytes.read 56 4 == 0 && bytes.read 60 4 == 0 &&
      bytes.read 64 4 == 24 && bytes.read 76 4 == 13

private def rejects (limits : Limits) (nullable : Bool) (values : List (Option KBytes))
    (expected : Error) : Bool :=
  match emitBinary limits nullable values with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard match emitBinary { dataBuffers := 0, bufferBytes := 17, outputBytes := 12 } false
    [some (.leaf 12 3)] with
  | .error _ => false
  | .ok output => output.buffers.payload.data.isEmpty && output.buffers.byteCount == 17

#guard rejects { rows := 0 } true [some .empty] .rowLimit
#guard rejects {} false [none] .nullInRequired
#guard rejects { valueBytes := 12 } true [some (.leaf 13 0)] .valueLimit
#guard rejects { valueBytes := 2^31 } true [some (.leaf (2^31) 0)] .signedExtent
#guard rejects { valueBytes := 2^31 } true [some (.leaf (2^31 - 1) 0), some (.leaf 13 0)] .signedExtent
#guard rejects { dataBuffers := 0 } true [some (.leaf 13 0)] .dataBufferLimit
#guard rejects { bufferBytes := 29 } true [some (.leaf 13 0)] .bufferBytesLimit
#guard rejects { outputBytes := 23 } true [some (.leaf 12 0), some (.leaf 12 0)] .outputBytesLimit
#guard rejects {} true [some (.node 1 .empty .empty)] .malformedSource

end Silmaril.Formats.Arrow.BinaryView.Column.Writer
