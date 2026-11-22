module

public import Silmaril.Formats.Blake3Cas.Defs
import Silmaril.Proofs.Formats.Blake3Cas.Soundness

public section

namespace Silmaril.Formats.Blake3Cas

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming.ByteRange (Slice Partial ofWhole)

theorem SpanFact.soundTrusted {size : Nat} {digest whole : Bytes} (fact : SpanFact size digest)
    (named : Named concrete digest whole) (extent : whole.length = size) :
    Slice whole fact.offset fact.bytes ∨ ConcreteCollision :=
  (fact.checked.sliceOrCollision named extent).imp id concrete_collision_iff.mp

theorem SpanFact.soundEOF {size : Nat} {digest whole : Bytes} (fact : SpanFact size digest)
    (eof : CheckedEOF concrete size digest) (named : Named concrete digest whole) :
    Slice whole fact.offset fact.bytes ∨ ConcreteCollision :=
  fact.checked.sliceOrConcreteCollisionOfEOF eof named

theorem Advance.releasedPosition {size before after : Nat} {digest : Bytes}
    {advance : Advance size digest before after} {fact : SpanFact size digest}
    (emitted : advance.released = some fact) :
    fact.offset = before ∧ before + fact.bytes.length = after ∧ 0 < fact.bytes.length :=
  Proofs.Formats.Blake3Cas.releasedPosition emitted

theorem RangeStep.releasedTrusted {size cursor : Nat} {digest input whole : Bytes}
    (step : RangeStep size digest input cursor) {fact : SpanFact size digest}
    (emitted : step.advance.released = some fact) (named : Named concrete digest whole)
    (extent : whole.length = size) : Slice whole cursor fact.bytes ∨ ConcreteCollision :=
  (step.advance.releasedPosition emitted).1 ▸ fact.soundTrusted named extent

theorem RangeStep.releasedEOF {size cursor : Nat} {digest input whole : Bytes}
    (step : RangeStep size digest input cursor) {fact : SpanFact size digest}
    (emitted : step.advance.released = some fact) (eof : CheckedEOF concrete size digest)
    (named : Named concrete digest whole) : Slice whole cursor fact.bytes ∨ ConcreteCollision :=
  (step.advance.releasedPosition emitted).1 ▸ fact.soundEOF eof named

theorem Coverage.exactLength {size before after : Nat} {digest : Bytes}
    (coverage : Coverage size digest before after) : before + coverage.bytes.length = after :=
  Proofs.Formats.Blake3Cas.coverageLength coverage

theorem Coverage.soundTrusted {size before after : Nat} {digest whole : Bytes}
    (coverage : Coverage size digest before after) (named : Named concrete digest whole)
    (extent : whole.length = size) (bound : after ≤ size) :
    Slice whole before coverage.bytes ∨ ConcreteCollision :=
  Proofs.Formats.Blake3Cas.coverageTrusted coverage named extent bound

theorem Coverage.soundEOF {size before after : Nat} {digest whole : Bytes}
    (coverage : Coverage size digest before after) (eof : CheckedEOF concrete size digest)
    (named : Named concrete digest whole) (bound : after ≤ size) :
    Slice whole before coverage.bytes ∨ ConcreteCollision :=
  (eof.concreteExtentOrCollision named).elim (fun extent => coverage.soundTrusted named extent.symm bound) Or.inr

theorem Prefix.wire {size before after : Nat} {digest input rest : Bytes}
    {request : Bao.RangeRequest} {initial final : Session size digest}
    (trace : Prefix request before initial input after final rest) :
    input = trace.fields.flatten ++ rest := Proofs.Formats.Blake3Cas.prefixWire trace

/-- The successful trusted-extent path yields a naming wrapper fact, or a
concrete collision against the supplied, actually named, reference. -/
theorem ExactRange.soundTrusted {size : Nat} {digest whole : Bytes} {request : Bao.RangeRequest}
    (range : ExactRange size digest request) (named : Named concrete digest whole)
    (extent : whole.length = size) :
    Partial (Named concrete) digest request.start range.coverage.bytes ∨ ConcreteCollision :=
  (range.coverage.soundTrusted named extent range.within).imp (ofWhole named) id

/-- No equality between the wire extent and the actual object's length is assumed. -/
theorem ExactRange.soundEOF {size : Nat} {digest whole : Bytes} {request : Bao.RangeRequest}
    (range : ExactRange size digest request) (eof : CheckedEOF concrete size digest)
    (named : Named concrete digest whole) :
    Partial (Named concrete) digest request.start range.coverage.bytes ∨ ConcreteCollision :=
  (range.coverage.soundEOF eof named range.within).imp (ofWhole named) id

theorem rangeFinished_spec {size cursor : Nat} {digest rest : Bytes} {request : Bao.RangeRequest}
    {state : Session size digest} {endOfFrame : Bool} :
    rangeFinished request cursor state rest endOfFrame = true ↔
      state.pending = [] ∧ rest = [] ∧ endOfFrame = true ∧
        cursor = request.start + request.count ∧ request.start + request.count ≤ size :=
  Proofs.Formats.Blake3Cas.rangeFinishedSpec

theorem Prefix.completed {size after : Nat} {digest input rest : Bytes} {request : Bao.RangeRequest}
    {initial final : Session size digest}
    (trace : Prefix request request.start initial input after final rest)
    (complete : rangeFinished request after final rest true = true) :
    Nonempty (ExactRange size digest request) :=
  let spec := (rangeFinished_spec.mp complete).2.2.2
  ⟨⟨spec.2, spec.1 ▸ trace.coverage⟩⟩

end Silmaril.Formats.Blake3Cas
