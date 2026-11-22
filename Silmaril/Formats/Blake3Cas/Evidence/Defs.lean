module

public import Silmaril.Crypto.Blake3.Range.EOF.Defs
public import Silmaril.Formats.Bao.Defs

@[expose] public section

namespace Silmaril.Formats.Blake3Cas

open Silmaril.Crypto.Blake3

/-- A checked path from a local CV to the external root. The base is a byte coordinate
in the kernel tree. Only the root and right descents retain the right-edge flag. -/
structure Anchor (size : Nat) (digest : Bytes) (shape : Shape) (root : Bool)
    (expected : CV) (base : Nat) (edge : Bool) : Prop where
  lift : ∀ {opening}, Trace concrete root shape opening expected →
    ∃ full, Root concrete size digest full ∧
      (∀ {offset fragment}, Read shape opening offset fragment →
        Read (geometry 0 size) full (base + offset) fragment) ∧
      (edge = true → opening.exposesEOF = true → full.exposesEOF = true)

/-- Coordinates are checked against the kernel subtree before a field is accepted. -/
def shapeSpan : Shape → Bao.Span
  | .leaf first _ => ⟨first, 1⟩
  | .fork left right =>
    let lhs := shapeSpan left
    ⟨lhs.first, lhs.count + (shapeSpan right).count⟩

def parentCV (root : Bool) (left right : CV) : CV := compress32 (parentInput root left right)

/-- Grouped data is disclosed through all its original 1 KiB kernel leaves, using
absolute chunk counters. -/
def subtreeCV? (root : Bool) (shape : Shape) (bytes : Bytes) : Option CV :=
  eval? (some ∘ compress32) root shape (disclose shape bytes)

/-- The input framing supplies the size check; the round-trip certifies every byte. -/
def parseCV (raw : Bytes) : Option {cv : CV // digestBytes cv = raw} := do
  let vector ← Bao.digest? raw
  let cv := loadWords (count := 8) vector
  if exactBytes : digestBytes cv = raw then some ⟨cv, exactBytes⟩ else none

end Silmaril.Formats.Blake3Cas
