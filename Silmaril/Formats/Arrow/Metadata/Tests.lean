module

import Silmaril.Formats.Arrow.Metadata.Thms
meta import Silmaril.Formats.Arrow.Metadata.Defs

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
