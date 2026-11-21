module

public import Silmaril.Crypto.Blake3.Range.EOF.Thms

@[expose] public section

namespace Silmaril.Crypto.Blake3

open Silmaril.Semantics.Naming.ByteRange (slice_iff)

/-- Compute an exact-length range and carry its kernel derivation. Opaque nodes cannot supply
bytes. This is a reference evaluator, not a streaming decoder. -/
def read? (shape : Shape) (opening : Opening) (offset count : Nat) :
    Option {fragment : Bytes // Read shape opening offset fragment ∧ fragment.length = count} :=
  match shape, opening with
  | .leaf chunk size, .leaf bytes =>
    if sized : bytes.length = size ∧ offset + count ≤ bytes.length then
      let fragment := (bytes.drop offset).take count
      have bound := sized.2
      have len : fragment.length = count := by simp [fragment]; omega
      have read := Read.leaf (chunk := chunk) sized.1 |>.sub
        (start := offset) (part := fragment) (slice_iff.mpr ⟨by omega, by rw [len]⟩)
      some ⟨fragment, by simpa only [Nat.zero_add] using read, len⟩
    else none
  | .fork left right, .fork lhs rhs =>
    if localRight : left.size ≤ offset then do
      let hit ← read? right rhs (offset - left.size) count
      let ⟨fragment, read, len⟩ := hit
      let atOffset : left.size + (offset - left.size) = offset := Nat.add_sub_of_le localRight
      return ⟨fragment, atOffset ▸ Read.right read, len⟩
    else if localLeft : offset + count ≤ left.size then do
      let ⟨fragment, read, len⟩ ← read? left lhs offset count
      return ⟨fragment, .left read, len⟩
    else do
      let ⟨before, lread, llen⟩ ← read? left lhs offset (left.size - offset)
      let ⟨after, rread, rlen⟩ ← read? right rhs 0 (count - (left.size - offset))
      return ⟨before ++ after, .join lread rread (by omega), by simp; omega⟩
  | _, _ => none

/-- Check a range while retaining the derivations indexed by the supplied opening. -/
def verifyRangeTrace? (run : Input → Option CV) (maxSize size : Nat) (digest : Bytes)
    (opening : Opening) (offset count : Nat) :
    Option {fragment : Bytes // Root (Compression.graph run) size digest opening ∧
      Read (geometry 0 size) opening offset fragment ∧ fragment.length = count} :=
  if size ≤ maxSize ∧ offset + count ≤ size then
    if hit : root? run size opening = some digest then do
      let ⟨fragment, read, len⟩ ← read? (geometry 0 size) opening offset count
      return ⟨fragment, root_graph.mp hit, read, len⟩
    else none
  else none

/-- Feed a decoded opening and a caller-chosen extent cap to the reference kernel. The cap is
checked before allocating the canonical geometry; it is not evidence of the actual length. -/
def verifyRange? (run : Input → Option CV) (maxSize size : Nat) (digest : Bytes)
    (opening : Opening) (offset count : Nat) :
    Option {fragment : Bytes // Checked (Compression.graph run) size digest offset fragment ∧ fragment.length = count} := do
  let ⟨fragment, root, read, len⟩ ← verifyRangeTrace? run maxSize size digest opening offset count
  return ⟨fragment, ⟨opening, root, read⟩, len⟩

/-- Check EOF independently, for example when a decoder receives the right edge separately. -/
def verifyEOF? (run : Input → Option CV) (maxSize size : Nat) (digest : Bytes) (opening : Opening) :
    Option (PLift (CheckedEOF (Compression.graph run) size digest)) :=
  if size ≤ maxSize then
    if edge : opening.exposesEOF = true then
      if hit : root? run size opening = some digest then some ⟨⟨opening, root_graph.mp hit, edge⟩⟩ else none
    else none
  else none

/-- Check a decoded opening that reveals both the requested range and the final chunk. -/
def verifyRangeWithEOF? (run : Input → Option CV) (maxSize size : Nat) (digest : Bytes)
    (opening : Opening) (offset count : Nat) :
    Option {fragment : Bytes // Checked (Compression.graph run) size digest offset fragment ∧
      CheckedEOF (Compression.graph run) size digest ∧ fragment.length = count} :=
  if edge : opening.exposesEOF = true then do
    let ⟨fragment, root, read, len⟩ ← verifyRangeTrace? run maxSize size digest opening offset count
    return ⟨fragment, ⟨opening, root, read⟩, ⟨opening, root, edge⟩, len⟩
  else none

end Silmaril.Crypto.Blake3
