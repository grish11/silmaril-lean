module

public import Silmaril.Semantics.Naming.ByteRange.Defs
import Silmaril.Proofs.Semantics.Naming.ByteRange

public section

namespace Silmaril.Semantics.Naming.ByteRange

theorem Slice.sub {whole fragment part : Bytes} {offset start : Nat}
    (outer : Slice whole offset fragment) (inner : Slice fragment start part) :
    Slice whole (offset + start) part := Proofs.Semantics.Naming.ByteRange.sub outer inner

theorem slice_iff {whole fragment : Bytes} {offset : Nat} :
    Slice whole offset fragment ↔
      offset + fragment.length ≤ whole.length ∧ (whole.drop offset).take fragment.length = fragment :=
  Proofs.Semantics.Naming.ByteRange.slice_iff

theorem ofWhole {Name : Type} {rel : Relation Name Bytes} {name : Name} {whole fragment : Bytes}
    {offset : Nat} (named : rel name whole) (slice : Slice whole offset fragment) :
    Partial rel name offset fragment := ⟨whole, named, slice⟩

theorem Partial.sub {Name : Type} {rel : Relation Name Bytes} {name : Name} {fragment part : Bytes}
    {offset start : Nat} (fact : Partial rel name offset fragment) (slice : Slice fragment start part) :
    Partial rel name (offset + start) part :=
  let ⟨_, named, outer⟩ := fact; ofWhole named (outer.sub slice)

end Silmaril.Semantics.Naming.ByteRange
