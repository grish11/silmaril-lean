module

public import Silmaril.Crypto.Blake3.Range.Defs

@[expose] public section

namespace Silmaril.Crypto.Blake3

/-- Follow the right edge to a disclosed chunk. The `Root` judgment, not this structural
test, checks that the path and chunk fit the canonical geometry of the claimed extent. -/
def Opening.exposesEOF : Opening → Bool
  | .opaque _ => false
  | .leaf _ => true
  | .fork _ right => right.exposesEOF

/-- A checked extent claim relative to a digest. This does not assert that a whole payload
exists: the left siblings of the EOF path may be opaque. -/
def CheckedEOF (rel : Compression) (size : Nat) (digest : Bytes) : Prop :=
  ∃ opening, Root rel size digest opening ∧ opening.exposesEOF = true

end Silmaril.Crypto.Blake3
