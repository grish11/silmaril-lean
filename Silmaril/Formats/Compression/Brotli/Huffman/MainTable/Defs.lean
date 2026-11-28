module

public import Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Defs

/-! Install the canonical table of an RFC 7932 §3.5 complex description
from a checked code-length table and the cursor at the main lengths. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Huffman.MainTable

structure Table where
  lengths : List Nat
  decoder : HuffmanTable
  installed : HuffmanTable.ofLengths lengths 15 = some decoder

inductive Error where
  | lengths (reason : MainLengths.Error)
  | invalidLengths
  deriving DecidableEq, Repr

namespace Internal

def install (lengths : List Nat) : Except Error Table :=
  match checked : HuffmanTable.ofLengths lengths 15 with
  | none => .error .invalidLengths
  | some decoder => .ok ⟨lengths, decoder, checked⟩

end Internal

/-- Install the shared canonical decoder. Table construction consumes no
    bits beyond those read by the checked main-length expansion. -/
def read (limits : MainLengths.Limits) (alphabet : Nat) (secondary : CodeLengths.Table)
    (before : LSBReader) : Except Error (Table × LSBReader) := do
  let (lengths, after) ← (MainLengths.read limits alphabet secondary before).mapError Error.lengths
  let table ← Internal.install lengths
  pure (table, after)

end Silmaril.Formats.Compression.Brotli.Huffman.MainTable
