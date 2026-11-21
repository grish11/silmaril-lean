module

public import Silmaril.Containers.Cas.Naming.Defs
public import Silmaril.Crypto.Blake3.Range.EOF.Thms

public section

namespace Silmaril.Containers.Cas.Store

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming (PartialHashCompatible)
open Silmaril.Semantics.Naming.ByteRange (Partial ofWhole)

/-- A compatible store hit supplies the actual named reference, not the opaque proof frontier. -/
theorem blake3_range {store : Store Bytes Bytes} {digest whole fragment : Bytes} {size offset : Nat}
    (compatible : PartialHashCompatible (hash? (some ∘ compress32)) store.relation)
    (hit : store digest = some whole) (length : whole.length = size)
    (checked : Checked concrete size digest offset fragment) :
    Partial store.relation digest offset fragment ∨ Compression.Collision concrete :=
  (checked.sliceOrCollision (Named.graph ▸ compatible hit) length).imp (ofWhole hit) id

/-- A compatible store hit is an actual named reference of arbitrary length. -/
theorem blake3_range_with_eof {store : Store Bytes Bytes} {digest whole fragment : Bytes} {size offset : Nat}
    (compatible : PartialHashCompatible (hash? (some ∘ compress32)) store.relation)
    (hit : store digest = some whole) (checked : Checked concrete size digest offset fragment)
    (eof : CheckedEOF concrete size digest) :
    Partial store.relation digest offset fragment ∨ ∃ left right : Input, left ≠ right ∧ compress32 left = compress32 right :=
  (checked.sliceOrConcreteCollisionOfEOF eof (Named.graph ▸ compatible hit)).imp (ofWhole hit) id

end Silmaril.Containers.Cas.Store
