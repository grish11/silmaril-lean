module

public import Silmaril.Formats.Arrow.Metadata.Thms
public import Silmaril.Formats.Arrow.DateValues.Defs
public meta import Silmaril.Formats.Arrow.Metadata.Defs
public meta import Silmaril.Formats.Arrow.DateValues.Defs

open Silmaril Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.SchemaReader (DateUnit)

private meta def hasError {α : Type} (result : Except Error α) (expected : Error) : Bool :=
  match result with
  | .ok _ => false
  | .error actual => actual == expected

#guard (DateUnit.normalize none).toOption == some .millisecond
#guard (DateUnit.normalize (some 0)).toOption == some .day
#guard (DateUnit.normalize (some 1)).toOption == some .millisecond
#guard hasError (DateUnit.normalize (some 2)) (.malformed .flatbuffer)
#guard hasError (DateUnit.normalize (some 65535)) (.malformed .flatbuffer)
#guard hasError (SchemaReader.readMessage {} (.leaf 0 0)) (.malformed .flatbuffer)
#guard hasError (SchemaReader.readMessage { metadataBytes := 1 } (.leaf 2 0)) (.limit .metadataBytes)
#guard hasError (SchemaReader.readMessage {} (.node 1 .empty .empty)) (.malformed .source)

-- PyArrow Date32 with explicit DAY, followed by Date64 with an omitted unit.
private meta def dates : KBytes :=
  KBytes.ofChunks 16 192
    [0x800050006000c000a000000000010, 0x800080000000c000401000000000a,
    0x2000000040000000800040000, 0x6000800140010000000140000005c,
    0x80100000000001000100000000c0007, 0x40000002400000010,
    0x73646e6f636573696c6c696d0000000c, 0x140010000000040004000400000000,
    0x1000100000000c000700000008, 0x40000001c0000001008000000,
    0x60000007961640000000300000000, 0x600060008]

#guard (SchemaReader.readMessage {} dates).toOption ==
  some ⟨.little, [⟨"day", false, .date .day⟩, ⟨"milliseconds", true, .date .millisecond⟩]⟩
#guard hasError (readMessage {} dates) (.unsupported (.fieldType 8))

namespace Silmaril.Formats.Arrow.SchemaReader.Tests

/-- Observe producer record bytes using the descriptor parsed from their Schema. -/
public meta def observesDateBatch (schemaBytes metadata body : KBytes) (expectedUnit : DateUnit)
    (dates : DateValues.Column) : Bool :=
  match SchemaReader.readMessage {} schemaBytes, Arrow.readMessage {} metadata with
  | .ok ⟨endian, [⟨_, nullable, .date unit⟩]⟩, .ok ⟨.recordBatch batch, bodyLength⟩ =>
    let decoder : DateValues.Unit := match unit with
      | .day => .day
      | .millisecond => .millisecond
    let descriptor : DateValues.Descriptor := ⟨8, unit.code, endian.code, nullable⟩
    unit == expectedUnit && bodyLength == body.len &&
      (DateValues.decodeBatch {} decoder descriptor batch body).toOption == some dates
  | _, _ => false

end Silmaril.Formats.Arrow.SchemaReader.Tests

-- PyArrow Date32 record fixture, parsed from its own Schema message.
private meta def dateBatch_schema : KBytes :=
  KBytes.ofChunks 16 120
    [0x800050006000c000a000000000010, 0x800080000000c000401000000000a,
    0x1000000040000000800040000, 0xc0007000600080014001000000014,
    0x10080100000000001000100000, 0x300000000000000040000001c,
    0x6000600080006000000a597e6, 0x0]

private meta def dateBatch_metadata : KBytes :=
  KBytes.ofChunks 16 136
    [0x500060016000c0000000000000014, 0x18000403000000000c000c0008,
    0xc0018000a00000000000000000018, 0x100000003c0000000a00080004,
    0x2000000000000000000000004, 0x10000000000000000,
    0x100000000000000008, 0x40000000100000000,
    0x1]

private meta def dateBatch_body : KBytes :=
  KBytes.ofChunks 16 24
    [0xffffffff000000000000000d, 0x2b08]

#guard SchemaReader.Tests.observesDateBatch dateBatch_schema dateBatch_metadata dateBatch_body
  .day [some ⟨1969, 12, 31⟩, none, some ⟨2000, 2, 29⟩, some ⟨1970, 1, 1⟩]
