module

public import Silmaril.Formats.Arrow.BinaryView.Column.Defs

/-! Produced by scripts/arrow-binary-view/writer_fixtures.py. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Column.Writer.Fixture

def binaryMixed : FieldNode × Buffers :=
  ⟨⟨5, 1⟩, ⟨.leaf 1 0x1e,
    ⟨.leaf 80 0x22000000006c696174000000180000001500000000000000000000000dffffffffffffffffffffffff0000000c0000000000000000000000000000000000000000000000000000000000000000, #[.leaf 79 0x786966667573207972616e6962206465726f6e67696c6961746c6961746c6961746c6961746c6961746c69617400000000000000000000000000786966657270207972616e6962206465726f6e6769]⟩⟩⟩

def binaryInline : FieldNode × Buffers :=
  ⟨⟨2, 0⟩, ⟨.leaf 0 0x0,
    ⟨.leaf 32 0xffffffffffffffffffffffff0000000c00000000000000000000000000000000, #[.leaf 0 0x0]⟩⟩⟩

def binaryNulls : FieldNode × Buffers :=
  ⟨⟨2, 2⟩, ⟨.leaf 1 0x0,
    ⟨.leaf 32 0x0, #[]⟩⟩⟩

def binaryEmpty : FieldNode × Buffers :=
  ⟨⟨0, 0⟩, ⟨.leaf 0 0x0,
    ⟨.leaf 0 0x0, #[]⟩⟩⟩

def utf8Mixed : FieldNode × Buffers :=
  ⟨⟨5, 1⟩, ⟨.leaf 1 0x1e,
    ⟨.leaf 80 0x2500000000e9aa9be90000001b0000001800000000a9c3a9c30000000da9c3a9c3a9c3a9c3a9c3a9c30000000c0000000000000000000000000000000000000000000000000000000000000000, #[.leaf 88 0xaa9be92078696666757320382d465455206465726f6e6769aa9be9aa9be9aa9be9aa9be9aa9be9aa9be9aa9be9aa9be9aa9be978a9c3a9c3a9c3a9c3a9c3a9c3aa9be92078696665727020382d465455206465726f6e6769]⟩⟩⟩

def utf8Inline : FieldNode × Buffers :=
  ⟨⟨2, 0⟩, ⟨.leaf 0 0x0,
    ⟨.leaf 32 0xa9c3a9c3a9c3a9c3a9c3a9c30000000c00000000000000000000000000000000, #[.leaf 0 0x0]⟩⟩⟩

def utf8Nulls : FieldNode × Buffers :=
  ⟨⟨2, 2⟩, ⟨.leaf 1 0x0,
    ⟨.leaf 32 0x0, #[]⟩⟩⟩

def utf8Empty : FieldNode × Buffers :=
  ⟨⟨0, 0⟩, ⟨.leaf 0 0x0,
    ⟨.leaf 0 0x0, #[]⟩⟩⟩

end Silmaril.Formats.Arrow.BinaryView.Column.Writer.Fixture
