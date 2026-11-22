module

public import Silmaril.Semantics.Naming.ByteRange.Defs

public section

namespace Silmaril.Proofs.Semantics.Naming.ByteRange

open Silmaril.Semantics.Naming.ByteRange

theorem sub {whole fragment part : Bytes} {offset start : Nat}
    (outer : Slice whole offset fragment) (inner : Slice fragment start part) :
    Slice whole (offset + start) part := by
  obtain ⟨before, after, rfl, rfl⟩ := outer
  obtain ⟨pre, post, rfl, rfl⟩ := inner
  exact ⟨before ++ pre, post ++ after, by simp [List.append_assoc], by simp⟩

theorem slice_iff {whole fragment : Bytes} {offset : Nat} :
    Slice whole offset fragment ↔
      offset + fragment.length ≤ whole.length ∧ (whole.drop offset).take fragment.length = fragment := by
  constructor
  · rintro ⟨before, after, rfl, rfl⟩
    simp [List.append_assoc]
  · rintro ⟨bound, read⟩
    refine ⟨whole.take offset, whole.drop (offset + fragment.length), ?_, by simp; omega⟩
    conv_lhs => rw [← List.take_append_drop offset whole]
    rw [← List.drop_drop, List.append_assoc]
    apply congrArg (whole.take offset ++ ·)
    exact (List.take_append_drop fragment.length (whole.drop offset)).symm.trans
      (congrArg (· ++ (whole.drop offset).drop fragment.length) read)

end Silmaril.Proofs.Semantics.Naming.ByteRange
