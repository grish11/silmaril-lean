module

import Silmaril.Formats.Arrow.BinaryView.Defs
meta import Silmaril.Formats.Arrow.BinaryView.Defs

open Silmaril Silmaril.Formats.Arrow.BinaryView

-- PyArrow 26.0.1 buffer fixtures, packed little-endian.
-- scripts/arrow-binary-view/fixtures.py checks their hashes and reproduction.
private def slots : KBytes :=
  .leaf 128 0xd00000001787a7978000000120000000000000001646362610000000d0000000d00000000aaa79ff0000000100000000000000000646362610000000d6c6b6a6968676665646362610000000c00000000000000000000b1ce0000000200000000000000000000000000000000

private def firstData : KBytes :=
  .leaf 29 0xaaa79ff0aaa79ff0aaa79ff0aaa79ff06d6c6b6a696867666564636261

private def secondData : KBytes :=
  .leaf 31 0x7a79787a79787a79787a79787a79787a79786d6c6b6a696867666564636261

private def buffers : Buffers := ⟨slots, #[firstData, secondData]⟩

private def expected : List String :=
  ["", "α", "abcdefghijkl", "abcdefghijklm", "🧪🧪🧪🧪", "abcdefghijklm", "xyzxyzxyzxyzxyzxyz"]

/- The first seven slots have their validity bits set. The final slot is
null and is outside the non-null slot reader's observation. -/
#guard ((List.range 7).mapM (fun i => readUtf8 buffers i 18)).toOption = some expected
#guard ((List.range 7).mapM (fun i => (readBinary buffers i 18).map KBytes.toList)).toOption =
  some (expected.map fun s => s.toUTF8.data.toList)

private def external (length leading bufferIndex offset : Nat) : KBytes :=
  KBytes.leaf 4 length ++ KBytes.leaf 4 leading ++
    KBytes.leaf 4 bufferIndex ++ KBytes.leaf 4 offset

private def repeated : Buffers :=
  ⟨slots.slice (16 * 3) 16 ++ slots.slice (16 * 3) 16, buffers.data⟩

#guard ([0, 1].mapM (fun i => readUtf8 repeated i 13)).toOption = some ["abcdefghijklm", "abcdefghijklm"]
private def rejected (result : Except Error String) (expected : Error) : Bool :=
  match result with
  | .error actual => decide (actual = expected)
  | .ok _ => false

#guard rejected (readUtf8 buffers 8 100) .truncatedSlot
#guard rejected (readUtf8 ⟨.leaf 15 0, #[]⟩ 0 100) .truncatedSlot
#guard rejected (readUtf8 ⟨.node 16 (.leaf 4 0) (.leaf 4 0), #[]⟩ 0 100) .malformedSource
#guard rejected (readUtf8 ⟨external (2^31) 0 0 0, buffers.data⟩ 0 100) .negativeLength
#guard rejected (readUtf8 buffers 3 12) .valueLimit
#guard rejected (readUtf8 ⟨external 0 1 0 0, #[]⟩ 0 100) .invalidPadding
#guard rejected (readUtf8 ⟨external 13 0 2 0, buffers.data⟩ 0 100) .invalidReference
#guard rejected (readUtf8 ⟨external 13 0 (2^31) 0, buffers.data⟩ 0 100) .invalidReference
#guard rejected (readUtf8 ⟨external 13 0 0 (2^31), buffers.data⟩ 0 100) .invalidReference
#guard rejected (readUtf8 ⟨external 13 0 0 17, buffers.data⟩ 0 100) .invalidReference
#guard rejected (readUtf8 ⟨external 13 0 0 0, #[.node 29 (.leaf 0 0) (.leaf 0 0)]⟩ 0 100) .malformedSource
#guard rejected (readUtf8 ⟨external 13 0 0 0, buffers.data⟩ 0 100) .prefixMismatch

private def invalidUtf8 : Buffers := ⟨external 1 255 0 0, #[]⟩

#guard ((readBinary invalidUtf8 0 1).map KBytes.toList).toOption = some [255]
#guard rejected (readUtf8 invalidUtf8 0 1) .invalidUtf8
