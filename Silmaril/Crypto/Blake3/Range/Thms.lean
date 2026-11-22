module

public import Silmaril.Crypto.Blake3.Range.Defs
public import Silmaril.Crypto.Blake3.Tree.Thms
public import Silmaril.Semantics.Naming.ByteRange.Thms
import Silmaril.Proofs.Crypto.Blake3.Agreement
import Silmaril.Proofs.Crypto.Blake3.Range

public section

namespace Silmaril.Crypto.Blake3

open Silmaril.Semantics.Naming.ByteRange (Slice)

theorem Trace.canonical {rel : Compression} (canonical : Compression.Canonical rel)
    {root : Bool} {shape : Shape} {opening : Opening} {left right : CV}
    (lhs : Trace rel root shape opening left) (rhs : Trace rel root shape opening right) : left = right :=
  Proofs.Crypto.Blake3.trace_canonical canonical lhs rhs

theorem Trace.agreeOrCollision {rel : Compression} {root : Bool} {shape : Shape} {lhs rhs : Opening} {output : CV}
    (left : Trace rel root shape lhs output) (right : Trace rel root shape rhs output) :
    Agree lhs rhs ∨ Compression.Collision rel := Proofs.Crypto.Blake3.trace_agree left right

theorem Root.agreeOrCollision {rel : Compression} {size : Nat} {digest : Bytes} {lhs rhs : Opening}
    (left : Root rel size digest lhs) (right : Root rel size digest rhs) :
    Agree lhs rhs ∨ Compression.Collision rel := Proofs.Crypto.Blake3.root_agree left right

theorem Trace.refine {rel : Compression} {shape : Shape} {lhs rhs : Opening} {root : Bool} {output : CV}
    (trace : Trace rel root shape lhs output) (refinement : Refines rel shape lhs rhs) :
    Trace rel root shape rhs output := Proofs.Crypto.Blake3.trace_refine refinement trace

theorem Root.refine {rel : Compression} {size : Nat} {digest : Bytes} {lhs rhs : Opening}
    (trace : Root rel size digest lhs) (refinement : Refines rel (geometry 0 size) lhs rhs) :
    Root rel size digest rhs :=
  let ⟨sizeOK, output, checked, digestEq⟩ := trace; ⟨sizeOK, output, checked.refine refinement, digestEq⟩

theorem Read.refine {rel : Compression} {shape : Shape} {lhs rhs : Opening} {offset : Nat} {fragment : Bytes}
    (read : Read shape lhs offset fragment) (refinement : Refines rel shape lhs rhs) : Read shape rhs offset fragment :=
  Proofs.Crypto.Blake3.read_refine read refinement

theorem Read.bound {shape : Shape} {opening : Opening} {offset : Nat} {fragment : Bytes}
    (read : Read shape opening offset fragment) : offset + fragment.length ≤ shape.size :=
  Proofs.Crypto.Blake3.read_bound read

theorem Named.graph {run : Input → Option CV} :
    Named (Compression.graph run) = Semantics.Naming.nameGraph (hash? run) :=
  funext fun _ => funext fun _ => propext root_graph.symm

theorem Checked.ofEval {rel : Compression} {run : Input → Option CV} {size offset : Nat}
    {digest fragment : Bytes} {opening : Opening} (consistent : Compression.Consistent rel run)
    (hit : root? run size opening = some digest) (read : Read (geometry 0 size) opening offset fragment) :
    Checked rel size digest offset fragment := ⟨opening, root_sound consistent hit, read⟩

theorem Checked.sub {rel : Compression} {size offset start : Nat} {digest fragment part : Bytes}
    (checked : Checked rel size digest offset fragment) (slice : Slice fragment start part) :
    Checked rel size digest (offset + start) part :=
  let ⟨opening, root, read⟩ := checked; ⟨opening, root, .sub read slice⟩

theorem Checked.bound {rel : Compression} {size offset : Nat} {digest fragment : Bytes}
    (checked : Checked rel size digest offset fragment) : offset + fragment.length ≤ size :=
  let ⟨_, _, read⟩ := checked; geometry_size 0 size ▸ read.bound

/-- The reference is any actually named payload with the same extent. A checked opening alone
does not assert that such a payload exists or independently authenticate the claimed extent. -/
theorem Checked.sliceOrCollision {rel : Compression} {size offset : Nat} {digest whole fragment : Bytes}
    (checked : Checked rel size digest offset fragment) (named : Named rel digest whole)
    (length : whole.length = size) : Slice whole offset fragment ∨ Compression.Collision rel :=
  Proofs.Crypto.Blake3.checked_slice_or_collision checked named length

theorem concrete_collision_iff : Compression.Collision concrete ↔
    ∃ left right : Input, left ≠ right ∧ compress32 left = compress32 right :=
  ⟨fun ⟨left, right, _, ne, lhs, rhs⟩ => ⟨left, right, ne, Option.some.inj (lhs.trans rhs.symm)⟩,
   fun ⟨left, right, ne, eq⟩ => ⟨left, right, compress32 right, ne, congrArg some eq, rfl⟩⟩

end Silmaril.Crypto.Blake3
