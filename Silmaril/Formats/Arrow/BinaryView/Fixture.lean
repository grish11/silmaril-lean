module

public import Silmaril.Formats.Arrow.BinaryView.Defs

@[expose] public section

namespace Silmaril.Formats.Arrow.BinaryView.Fixture

-- PyArrow 26.0.1 buffer fixtures, packed little-endian.
-- scripts/arrow-binary-view/fixtures.py checks their hashes and reproduction.
def slots : KBytes :=
  .leaf 128 0xd00000001787a7978000000120000000000000001646362610000000d0000000d00000000aaa79ff0000000100000000000000000646362610000000d6c6b6a6968676665646362610000000c00000000000000000000b1ce0000000200000000000000000000000000000000

def firstData : KBytes :=
  .leaf 29 0xaaa79ff0aaa79ff0aaa79ff0aaa79ff06d6c6b6a696867666564636261

def secondData : KBytes :=
  .leaf 31 0x7a79787a79787a79787a79787a79787a79786d6c6b6a696867666564636261

def validity : KBytes :=
  .leaf 1 0x7f

def buffers : BinaryView.Buffers := ⟨slots, #[firstData, secondData]⟩

def expected : List String :=
  ["", "α", "abcdefghijkl", "abcdefghijklm", "🧪🧪🧪🧪", "abcdefghijklm", "xyzxyzxyzxyzxyzxyz"]

end Silmaril.Formats.Arrow.BinaryView.Fixture
