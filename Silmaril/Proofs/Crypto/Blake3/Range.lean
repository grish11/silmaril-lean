module

public import Silmaril.Crypto.Blake3.Range.Defs
public import Silmaril.Semantics.Naming.ByteRange.Thms
import Silmaril.Proofs.Crypto.Blake3.Agreement
import Silmaril.Proofs.Crypto.Blake3.Evaluation

public section

namespace Silmaril.Proofs.Crypto.Blake3

open Silmaril.Crypto.Blake3
open Silmaril.Semantics.Naming.ByteRange (Slice slice_iff)

theorem read_bound {shape : Shape} {opening : Opening} {offset : Nat} {fragment : Bytes}
    (read : Read shape opening offset fragment) : offset + fragment.length ≤ shape.size := by
  induction read with
  | leaf len => simpa [Shape.size] using Nat.le_of_eq len
  | left _ ih => simp [Shape.size]; omega
  | right _ ih => simp [Shape.size]; omega
  | join _ _ _ _ rightIH => simp [Shape.size] at *; omega
  | sub _ inner ih => have := (slice_iff.mp inner).1; omega

theorem trace_refine {rel : Compression} {shape : Shape} {lhs rhs : Opening}
    {root : Bool} {output : CV} (refinement : Refines rel shape lhs rhs)
    (trace : Trace rel root shape lhs output) : Trace rel root shape rhs output := by
  induction refinement generalizing root output with
  | keep => exact trace
  | expose opened => cases trace; exact opened
  | fork _ _ leftIH rightIH =>
    cases trace with
    | fork ltrace rtrace hit => exact .fork (leftIH ltrace) (rightIH rtrace) hit

theorem read_refine {rel : Compression} {shape : Shape} {lhs rhs : Opening} {offset : Nat} {fragment : Bytes}
    (read : Read shape lhs offset fragment) (refinement : Refines rel shape lhs rhs) : Read shape rhs offset fragment := by
  induction read generalizing rhs with
  | leaf len => cases refinement with | keep => exact .leaf len
  | left original ih =>
    cases refinement with
    | keep => exact .left original
    | fork left _ => exact .left (ih left)
  | right original ih =>
    cases refinement with
    | keep => exact .right original
    | fork _ right => exact .right (ih right)
  | join lhs rhs adjacent leftIH rightIH =>
    cases refinement with
    | keep => exact .join lhs rhs adjacent
    | fork left right => exact .join (leftIH left) (rightIH right) adjacent
  | sub _ slice ih => exact .sub (ih refinement) slice

private theorem read_transfer {shape : Shape} {lhs rhs : Opening} {offset : Nat} {fragment : Bytes}
    (read : Read shape lhs offset fragment) (agree : Agree lhs rhs)
    (whole : Bytes) (disclosed : rhs = disclose shape whole) : Read shape rhs offset fragment := by
  induction read generalizing rhs whole with
  | leaf len =>
    subst rhs
    cases agree with
    | leaf => exact .leaf len
  | left _ ih =>
    subst rhs
    cases agree with
    | fork lh _ => exact .left (ih lh _ rfl)
  | right _ ih =>
    subst rhs
    cases agree with
    | fork _ rh => exact .right (ih rh _ rfl)
  | join _ _ atBoundary leftIH rightIH =>
    subst rhs
    cases agree with
    | fork lh rh => exact .join (leftIH lh _ rfl) (rightIH rh _ rfl) atBoundary
  | sub _ inner ih => exact .sub (ih agree whole disclosed) inner

private theorem slice_append {left right before after : Bytes} {offset : Nat}
    (lhs : Slice left offset before) (rhs : Slice right 0 after) (adjacent : offset + before.length = left.length) :
    Slice (left ++ right) offset (before ++ after) := by
  obtain ⟨pre, post, rfl, hpre⟩ := lhs
  obtain ⟨preRight, postRight, rfl, hright⟩ := rhs
  have postEmpty : post = [] := by
    apply List.length_eq_zero_iff.mp
    simp only [List.length_append] at adjacent
    omega
  have preEmpty := List.length_eq_zero_iff.mp hright
  exact ⟨pre, postRight, by simp [postEmpty, preEmpty, List.append_assoc], hpre⟩

theorem read_disclose {shape : Shape} {opening : Opening} {whole fragment : Bytes} {offset : Nat}
    (read : Read shape opening offset fragment) (disclosed : opening = disclose shape whole)
    (len : whole.length = shape.size) : Slice whole offset fragment := by
  induction read generalizing whole with
  | leaf =>
    cases disclosed
    exact ⟨[], [], by simp, rfl⟩
  | @left left right lhs rhs offset bytes _ ih =>
    injection disclosed with hl _
    have size : (whole.take left.size).length = left.size := by
      simp [Shape.size] at len
      simp; omega
    simpa only [Nat.zero_add] using Slice.sub (whole := whole) (offset := 0)
      ⟨[], whole.drop left.size, by simp, rfl⟩ (ih hl size)
  | @right left right lhs rhs offset bytes _ ih =>
    injection disclosed with _ hr
    have size : (whole.drop left.size).length = right.size := by
      simp [Shape.size] at len
      simp; omega
    exact Slice.sub ⟨whole.take left.size, [], by simp, by simp [Shape.size] at len; simp; omega⟩ (ih hr size)
  | @join left right lhs rhs offset before after _ _ atBoundary leftIH rightIH =>
    injection disclosed with hl hr
    have lsize : (whole.take left.size).length = left.size := by
      simp [Shape.size] at len
      simp; omega
    have rsize : (whole.drop left.size).length = right.size := by
      simp [Shape.size] at len
      simp; omega
    have adjacent : offset + before.length = (whole.take left.size).length := atBoundary.trans lsize.symm
    simpa only [List.take_append_drop] using slice_append (leftIH hl lsize) (rightIH hr rsize) adjacent
  | sub _ inner ih => exact (ih disclosed len).sub inner

theorem checked_slice_or_collision {rel : Compression} {size : Nat} {digest whole fragment : Bytes} {offset : Nat}
    (checked : Checked rel size digest offset fragment) (named : Named rel digest whole)
    (length : whole.length = size) : Slice whole offset fragment ∨ Compression.Collision rel := by
  obtain ⟨opening, opened, read⟩ := checked
  have actual : Root rel size digest (disclose (geometry 0 size) whole) := by
    rw [← length]
    exact named
  rcases root_agree opened actual with agree | collision
  · exact .inl (read_disclose (read_transfer read agree whole rfl) rfl (length.trans (geometry_size 0 size).symm))
  · exact .inr collision

end Silmaril.Proofs.Crypto.Blake3
