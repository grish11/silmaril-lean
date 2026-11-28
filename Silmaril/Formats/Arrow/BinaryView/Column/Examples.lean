module

import Silmaril.Formats.Arrow.BinaryView.Column.Defs
meta import Silmaril.Formats.Arrow.BinaryView.Column.Defs
import Silmaril.Formats.Arrow.BinaryView.Fixture
meta import Silmaril.Formats.Arrow.BinaryView.Fixture

open Silmaril Silmaril.Formats
open Silmaril.Formats.Arrow.BinaryView.Fixture
open Silmaril.Formats.Arrow.BinaryView.Column

private def column : Buffers := ⟨validity, buffers⟩

private def expectedColumn : List (Option String) := expected.map some ++ [none]

#guard (readUtf8 {} ⟨8, 1⟩ true column).toOption = some expectedColumn
#guard ((readBinary {} ⟨8, 1⟩ true column).map (·.map (·.map KBytes.toList))).toOption =
  some (expectedColumn.map (·.map fun s => s.toUTF8.data.toList))

/- The unused view in a null slot can contain any payload. The bitmap
still has to cover every logical slot. -/
private def nullGarbage : Buffers :=
  ⟨.leaf 1 0, ⟨.leaf 16 0xffffffff, #[]⟩⟩

#guard (readUtf8 {} ⟨1, 1⟩ true nullGarbage).toOption = some [none]
#guard (readUtf8 {} ⟨0, 0⟩ false ⟨.empty, ⟨.empty, #[]⟩⟩).toOption = some []
#guard (readUtf8 {} ⟨7, 0⟩ false { column with validity := .empty }).toOption =
  some (expected.map some)

private def padded : Buffers :=
  { column with payload := { column.payload with views := column.payload.views ++ .leaf 8 0 } }

#guard (readUtf8 {} ⟨8, 1⟩ true padded).toOption = some expectedColumn

private def rejects (result : Except Error (List (Option String))) (expected : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard rejects (readUtf8 { rows := 7 } ⟨8, 1⟩ true column) .rowLimit
#guard rejects (readUtf8 { dataBuffers := 1 } ⟨8, 1⟩ true column) .dataBufferLimit
#guard rejects (readUtf8 { bufferBytes := 188 } ⟨8, 1⟩ true column) .bufferBytesLimit
#guard rejects (readUtf8 { valueBytes := 12 } ⟨8, 1⟩ true column) (.slot 3 .valueLimit)
#guard rejects (readUtf8 {} ⟨9, 1⟩ true column) .invalidBitmap
#guard rejects (readUtf8 {} ⟨9, 0⟩ false { column with validity := .empty }) .truncatedViews
#guard rejects (readUtf8 {} ⟨8, 0⟩ true column) .invalidNullCount
#guard rejects (readUtf8 {} ⟨8, 1⟩ false column) .invalidNullCount
#guard rejects (readUtf8 {} ⟨8, 1⟩ true { column with validity := .empty }) .invalidNullCount
#guard rejects (readUtf8 {} ⟨8, 9⟩ true column) .invalidNullCount

private def repeatLong : Buffers :=
  let view := slots.slice (16 * 3) 16
  ⟨.empty, { buffers with views := view ++ view }⟩

#guard rejects (readUtf8 { outputBytes := 25 } ⟨2, 0⟩ false repeatLong) .outputBytesLimit
#guard (readUtf8 { outputBytes := 26 } ⟨2, 0⟩ false repeatLong).toOption =
  some [some "abcdefghijklm", some "abcdefghijklm"]
#guard rejects (readUtf8 {} ⟨1, 0⟩ false ⟨.empty, ⟨.leaf 16 0xff00000001, #[]⟩⟩) .invalidUtf8
