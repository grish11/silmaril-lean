module

public import Silmaril.Formats.Blake3Cas.Defs

public section

namespace Silmaril.Proofs.Formats.Blake3Cas

open Silmaril.Crypto.Blake3
open Silmaril.Formats
open Silmaril.Formats.Blake3Cas
open Silmaril.Semantics.Naming.ByteRange (Slice slice_iff)

theorem coverageLength {size before after : Nat} {digest : Bytes}
    (coverage : Coverage size digest before after) : before + coverage.bytes.length = after := by
  induction coverage with
  | nil => simp [Coverage.bytes]
  | cons head tail ih => cases head <;> simpa [Coverage.bytes, Advance.bytes, Nat.add_assoc] using ih

private theorem joinSlices {whole left right : Bytes} {offset : Nat}
    (lhs : Slice whole offset left) (rhs : Slice whole (offset + left.length) right) :
    Slice whole offset (left ++ right) := by
  obtain ⟨_, hl⟩ := slice_iff.mp lhs
  obtain ⟨bound, hr⟩ := slice_iff.mp rhs
  exact slice_iff.mpr ⟨by simpa [List.length_append, Nat.add_assoc] using bound,
    by simp [List.take_add, hl, hr]⟩

theorem coverageTrusted {size before after : Nat} {digest whole : Bytes}
    (coverage : Coverage size digest before after) (named : Named concrete digest whole)
    (extent : whole.length = size) (bound : after ≤ size) :
    Slice whole before coverage.bytes ∨ ConcreteCollision := by
  induction coverage with
  | nil offset =>
    exact .inl (slice_iff.mpr ⟨by simpa [Coverage.bytes, extent] using bound, by simp [Coverage.bytes]⟩)
  | cons head tail ih =>
    cases head with
    | skip => simpa [Coverage.bytes, Advance.bytes] using ih bound
    | take bytes _ checked =>
      rcases checked.sliceOrCollision named extent with lhs | collision
      · exact (ih bound).imp (fun rhs => joinSlices lhs rhs) id
      · exact .inr (concrete_collision_iff.mp collision)

theorem releasedPosition {size before after : Nat} {digest : Bytes}
    {advance : Advance size digest before after} {fact : SpanFact size digest}
    (emitted : advance.released = some fact) :
    fact.offset = before ∧ before + fact.bytes.length = after ∧ 0 < fact.bytes.length := by
  cases advance with
  | skip => simp [Advance.released] at emitted
  | take bytes nonempty checked =>
    simp only [Advance.released, Option.some.injEq] at emitted
    subst fact
    exact ⟨rfl, rfl, nonempty⟩

theorem prefixWire {size before after : Nat} {digest input rest : Bytes}
    {request : Bao.RangeRequest} {initial final : Session size digest}
    (trace : Prefix request before initial input after final rest) :
    input = trace.fields.flatten ++ rest := by
  induction trace with
  | nil => simp [Prefix.fields]
  | @cons before after initial final input rest step _ _ ih =>
    simpa [Prefix.fields, ih, List.append_assoc] using step.raw.wire

theorem rangeFinishedSpec {size cursor : Nat} {digest rest : Bytes} {request : Bao.RangeRequest}
    {state : Session size digest} {endOfFrame : Bool} :
    rangeFinished request cursor state rest endOfFrame = true ↔
      state.pending = [] ∧ rest = [] ∧ endOfFrame = true ∧
        cursor = request.start + request.count ∧ request.start + request.count ≤ size := by
  simp only [rangeFinished, finished, Bao.strictBounds, Bool.and_eq_true, List.isEmpty_iff,
    beq_iff_eq, decide_eq_true_eq, and_assoc]
  constructor
  · rintro ⟨pending, empty, frame, atEnd, lower, length⟩
    exact ⟨pending, empty, frame, atEnd, by omega⟩
  · rintro ⟨pending, empty, frame, atEnd, length⟩
    exact ⟨pending, empty, frame, atEnd, by omega, by omega⟩

end Silmaril.Proofs.Formats.Blake3Cas
