module

public import Silmaril.Formats.Bao.Opening.Defs

public section

namespace Silmaril.Proofs.Formats.Bao

open Silmaril.Formats.Bao

theorem fillFrontier_spec {expected : Digest} {plan : Plan} {fields rest : List Bytes}
    {frontier : Frontier} : fillFrontier expected plan fields = some (frontier, rest) ↔
      Fills expected plan fields frontier rest := by
  constructor
  · induction plan generalizing expected fields frontier rest with
    | skip => intro filled; cases filled; exact .skip
    | leaf span width =>
      cases fields with
      | nil => intro filled; cases filled; exact .unread
      | cons field tail =>
        intro filled
        by_cases widthEq : field.length = width
        · simp [fillFrontier, widthEq] at filled
          obtain ⟨rfl, rfl⟩ := filled
          exact .data widthEq
        · simp [fillFrontier, widthEq] at filled
    | fork span left right leftIH rightIH =>
      cases fields with
      | nil => intro filled; cases filled; exact .unread
      | cons field fields =>
        intro filled
        cases pair : splitPair field with
        | none => simp [fillFrontier, pair] at filled
        | some pairCVs =>
          obtain ⟨leftCV, rightCV⟩ := pairCVs
          cases leftEq : fillFrontier leftCV left fields with
          | none => simp [fillFrontier, pair, leftEq] at filled
          | some leftResult =>
            obtain ⟨lhs, middle⟩ := leftResult
            cases rightEq : fillFrontier rightCV right middle with
            | none => simp [fillFrontier, pair, leftEq, rightEq] at filled
            | some rightResult =>
              obtain ⟨rhs, tail⟩ := rightResult
              simp [fillFrontier, pair, leftEq, rightEq] at filled
              obtain ⟨rfl, rfl⟩ := filled
              exact .fork pair (leftIH leftEq) (rightIH rightEq)
  · intro filled
    induction filled with
    | skip => rfl
    | @unread _ plan => cases plan <;> rfl
    | data widthEq => simp [fillFrontier, widthEq]
    | fork pair _ _ leftIH rightIH => simp [fillFrontier, pair, leftIH, rightIH]

theorem lowerPrefix_spec {expected : Digest} {plan : Plan} {fields : List Bytes}
    {frontier : Frontier} : lowerPrefix plan expected fields = some frontier ↔
      Fills expected plan fields frontier [] ∧ (∀ cv, frontier ≠ .opaque cv) := by
  constructor
  · intro lowered
    cases filled : fillFrontier expected plan fields with
    | none => simp [lowerPrefix, filled] at lowered
    | some result =>
      obtain ⟨candidate, rest⟩ := result
      cases candidate <;> cases rest <;> simp [lowerPrefix, filled] at lowered
      all_goals subst frontier; exact ⟨fillFrontier_spec.mp filled, by simp⟩
  · rintro ⟨fills, notOpaque⟩
    have filled := fillFrontier_spec.mpr fills
    cases frontier with
    | «opaque» cv => exact False.elim (notOpaque cv rfl)
    | data => simp [lowerPrefix, filled]
    | fork => simp [lowerPrefix, filled]

theorem split_matches_byte_geometry (first size : Nat) (positive : 0 < size) :
    ((Span.mk first (chunks size)).split.2.first, (Span.mk first (chunks size)).split.1.count) =
      (first + 2 ^ ((size - 1) / chunkBytes).log2, 2 ^ ((size - 1) / chunkBytes).log2) := by
  have lastChunk : chunks size - 1 = (size - 1) / chunkBytes := by
    unfold chunks chunkBytes
    omega
  simp [Span.split, lastChunk]

theorem releaseRanges_spec {Range : Digest → Nat → Nat → Bytes → Prop}
    {Trusted EOF : Digest → Nat → Prop} {digest : Digest} {claim : Nat}
    {permit : Option (PLift (ExtentEvidence Trusted EOF digest claim))}
    {pending : List (StagedRange Range digest claim)} {output : List (Nat × Bytes)} :
    releaseRanges permit pending = some output ↔
      permit.isSome = true ∧ output = pending.map (fun fragment => (fragment.offset, fragment.bytes)) := by
  cases permit <;> simp [releaseRanges, eq_comm]

theorem released_slice_or_collision {Range : Digest → Nat → Nat → Bytes → Prop}
    {Trusted EOF : Digest → Nat → Prop} {digest : Digest} {claim referenceSize : Nat}
    {permit : Option (PLift (ExtentEvidence Trusted EOF digest claim))}
    {pending : List (StagedRange Range digest claim)} {output : List (Nat × Bytes)}
    {Slice : Nat → Bytes → Prop} {Collision : Prop}
    (trustedExtent : Trusted digest claim → claim = referenceSize)
    (checkedExtent : EOF digest claim → claim = referenceSize ∨ Collision)
    (sameExtent : ∀ {offset bytes}, Range digest claim offset bytes → claim = referenceSize →
      Slice offset bytes ∨ Collision)
    (released : releaseRanges permit pending = some output) :
    ∀ entry ∈ output, Slice entry.1 entry.2 ∨ Collision := by
  obtain ⟨present, rfl⟩ := releaseRanges_spec.mp released
  have extent : claim = referenceSize ∨ Collision := by
    cases permit with
    | none => simp at present
    | some certificate =>
      cases certificate.down with
      | trusted known => exact .inl (trustedExtent known)
      | checkedEOF known => exact checkedExtent known
  intro entry found
  obtain ⟨fragment, _, rfl⟩ := List.mem_map.mp found
  exact extent.elim (sameExtent fragment.checked) Or.inr

end Silmaril.Proofs.Formats.Bao
