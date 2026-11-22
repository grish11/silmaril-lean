module

public import Silmaril.Containers.Cas.Blake3.Thms
public import Silmaril.Formats.Blake3Cas.Thms

public section

namespace Silmaril.Containers.Cas.Store

open Silmaril.Crypto.Blake3
open Silmaril.Formats.Blake3Cas (SpanFact ExactRange ConcreteCollision)
open Silmaril.Semantics.Naming (PartialHashCompatible)
open Silmaril.Semantics.Naming.ByteRange (Partial ofWhole)

theorem blake3_wire_trusted {store : Store Bytes Bytes} {digest whole : Bytes} {size : Nat}
    {request : Formats.Bao.RangeRequest}
    (compatible : PartialHashCompatible (hash? (some ∘ compress32)) store.relation)
    (hit : store digest = some whole) (extent : whole.length = size) (range : ExactRange size digest request) :
    Partial store.relation digest request.start range.coverage.bytes ∨ ConcreteCollision :=
  (range.coverage.soundTrusted (Named.graph ▸ compatible hit) extent range.within).imp (ofWhole hit) id

theorem blake3_wire_eof {store : Store Bytes Bytes} {digest whole : Bytes} {size : Nat}
    {request : Formats.Bao.RangeRequest}
    (compatible : PartialHashCompatible (hash? (some ∘ compress32)) store.relation)
    (hit : store digest = some whole) (range : ExactRange size digest request)
    (eof : CheckedEOF concrete size digest) :
    Partial store.relation digest request.start range.coverage.bytes ∨ ConcreteCollision :=
  (range.coverage.soundEOF eof (Named.graph ▸ compatible hit) range.within).imp (ofWhole hit) id

/-- The checked emission is independent of any later proof or framing failure. -/
theorem blake3_wire_span_trusted {store : Store Bytes Bytes} {digest whole : Bytes} {size : Nat}
    (compatible : PartialHashCompatible (hash? (some ∘ compress32)) store.relation)
    (hit : store digest = some whole) (extent : whole.length = size) (span : SpanFact size digest) :
    Partial store.relation digest span.offset span.bytes ∨ ConcreteCollision :=
  (span.soundTrusted (Named.graph ▸ compatible hit) extent).imp (ofWhole hit) id

theorem blake3_wire_span_eof {store : Store Bytes Bytes} {digest whole : Bytes} {size : Nat}
    (compatible : PartialHashCompatible (hash? (some ∘ compress32)) store.relation)
    (hit : store digest = some whole) (span : SpanFact size digest) (eof : CheckedEOF concrete size digest) :
    Partial store.relation digest span.offset span.bytes ∨ ConcreteCollision :=
  (span.soundEOF eof (Named.graph ▸ compatible hit)).imp (ofWhole hit) id

end Silmaril.Containers.Cas.Store
