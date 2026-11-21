module

public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Naming.ByteRange

abbrev Bytes := List UInt8

/-- A fragment at a byte offset. The empty range at EOF is valid, not past EOF. -/
def Slice (whole : Bytes) (offset : Nat) (fragment : Bytes) : Prop :=
  ∃ before after : Bytes, whole = before ++ fragment ++ after ∧ before.length = offset

/-- A partial fact backed by a whole payload, for any naming relation. -/
def Partial {Name : Type} (rel : Relation Name Bytes) (name : Name)
    (offset : Nat) (fragment : Bytes) : Prop :=
  ∃ whole, rel name whole ∧ Slice whole offset fragment

end Silmaril.Semantics.Naming.ByteRange
