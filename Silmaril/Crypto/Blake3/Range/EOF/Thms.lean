module

public import Silmaril.Crypto.Blake3.Range.EOF.Defs
public import Silmaril.Crypto.Blake3.Range.Thms
import Silmaril.Proofs.Crypto.Blake3.Range.EOF

public section

namespace Silmaril.Crypto.Blake3

open Silmaril.Semantics.Naming.ByteRange (Slice)

theorem disclose_exposesEOF (shape : Shape) (bytes : Bytes) : (disclose shape bytes).exposesEOF = true :=
  Proofs.Crypto.Blake3.disclose_exposesEOF shape bytes

/-- Comparing two checked right-edge paths needs no shared extent or tree shape. -/
theorem Root.extentOrCollision {rel : Compression} {left right : Nat} {digest : Bytes} {lhs rhs : Opening}
    (lh : Root rel left digest lhs) (le : lhs.exposesEOF = true)
    (rh : Root rel right digest rhs) (re : rhs.exposesEOF = true) : left = right ∨ Compression.Collision rel :=
  Proofs.Crypto.Blake3.root_extent_or_collision lh le rh re

theorem Named.checkedEOF {rel : Compression} {digest whole : Bytes} (named : Named rel digest whole) :
    CheckedEOF rel whole.length digest := ⟨_, named, disclose_exposesEOF _ _⟩

/-- Full binding-or-collision for the supported naming profile, across arbitrary lengths. -/
theorem Named.eqOrCollision {rel : Compression} {digest left right : Bytes}
    (lh : Named rel digest left) (rh : Named rel digest right) : left = right ∨ Compression.Collision rel :=
  Proofs.Crypto.Blake3.named_eq_or_collision lh rh

/-- Any actually named object is a reference for a checked EOF; it need not match the claim's
length before comparison. -/
theorem CheckedEOF.extentOrCollision {rel : Compression} {size : Nat} {digest whole : Bytes}
    (checked : CheckedEOF rel size digest) (named : Named rel digest whole) :
    size = whole.length ∨ Compression.Collision rel :=
  let ⟨_, opened, edge⟩ := checked; opened.extentOrCollision edge named (disclose_exposesEOF _ _)

theorem CheckedEOF.concreteExtentOrCollision {size : Nat} {digest whole : Bytes}
    (checked : CheckedEOF concrete size digest) (named : Named concrete digest whole) :
    size = whole.length ∨ ∃ left right : Input, left ≠ right ∧ compress32 left = compress32 right :=
  (checked.extentOrCollision named).imp id concrete_collision_iff.mp

/-- EOF and range facts may come from separate openings, but must share the claim and digest. -/
theorem Checked.sliceOrCollisionOfEOF {rel : Compression} {size offset : Nat} {digest whole fragment : Bytes}
    (checked : Checked rel size digest offset fragment) (eof : CheckedEOF rel size digest)
    (named : Named rel digest whole) : Slice whole offset fragment ∨ Compression.Collision rel :=
  (eof.extentOrCollision named).elim (fun eq => checked.sliceOrCollision named eq.symm) Or.inr

theorem Checked.sliceOrConcreteCollisionOfEOF {size offset : Nat} {digest whole fragment : Bytes}
    (checked : Checked concrete size digest offset fragment) (eof : CheckedEOF concrete size digest)
    (named : Named concrete digest whole) :
    Slice whole offset fragment ∨ ∃ left right : Input, left ≠ right ∧ compress32 left = compress32 right :=
  (checked.sliceOrCollisionOfEOF eof named).imp id concrete_collision_iff.mp

end Silmaril.Crypto.Blake3
