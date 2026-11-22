module

public import Silmaril.Crypto.Blake3.Tree.Defs
public import Silmaril.Semantics.Naming.ByteRange.Defs

@[expose] public section

namespace Silmaril.Crypto.Blake3

open Silmaril.Semantics.Naming.ByteRange (Slice)

/-- Opaque nodes disclose no bytes. Agreement is on the overlap of disclosures. -/
inductive Agree : Opening → Opening → Prop where
  | opaqueLeft (cv) (right) : Agree (.opaque cv) right
  | opaqueRight (left) (cv) : Agree left (.opaque cv)
  | leaf (bytes) : Agree (.leaf bytes) (.leaf bytes)
  | fork {lhs rhs left right} : Agree lhs left → Agree rhs right → Agree (.fork lhs rhs) (.fork left right)

/-- Replace only opaque CVs, using non-ROOT traces at their already committed geometry. -/
inductive Refines (rel : Compression) : Shape → Opening → Opening → Prop where
  | keep (shape opening) : Refines rel shape opening opening
  | expose {shape cv opening} : Trace rel false shape opening cv → Refines rel shape (.opaque cv) opening
  | fork {left right lhs rhs newLeft newRight} : Refines rel left lhs newLeft → Refines rel right rhs newRight →
      Refines rel (.fork left right) (.fork lhs rhs) (.fork newLeft newRight)

/-- Byte coordinates are relative to the indexed subtree, not attacker-provided labels.
Crossing a child boundary requires an adjacent suffix and prefix. -/
inductive Read : Shape → Opening → Nat → Bytes → Prop where
  | leaf {chunk size bytes} : bytes.length = size → Read (.leaf chunk size) (.leaf bytes) 0 bytes
  | left {left right lhs rhs offset bytes} : Read left lhs offset bytes →
      Read (.fork left right) (.fork lhs rhs) offset bytes
  | right {left right lhs rhs offset bytes} : Read right rhs offset bytes →
      Read (.fork left right) (.fork lhs rhs) (left.size + offset) bytes
  | join {left right lhs rhs offset before after} : Read left lhs offset before → Read right rhs 0 after →
      offset + before.length = left.size → Read (.fork left right) (.fork lhs rhs) offset (before ++ after)
  | sub {shape opening offset bytes start part} : Read shape opening offset bytes → Slice bytes start part →
      Read shape opening (offset + start) part

/-- A whole payload names itself exactly when a fully disclosed ROOT trace produces its name. -/
def Named (rel : Compression) : Semantics.Naming.Relation Bytes Bytes :=
  fun digest bytes => Root rel bytes.length digest (disclose (geometry 0 bytes.length) bytes)

/-- A kernel judgment, not an existential claim about the contents behind an opaque CV. -/
def Checked (rel : Compression) (size : Nat) (digest : Bytes) (offset : Nat) (fragment : Bytes) : Prop :=
  ∃ opening, Root rel size digest opening ∧ Read (geometry 0 size) opening offset fragment

end Silmaril.Crypto.Blake3
