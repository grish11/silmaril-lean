module

public import Silmaril.Prelude.Bytes.Write.Thms
import Init.Omega

@[expose] public section

namespace Silmaril.Proofs.Formats.Arrow.StreamWriter

theorem append_length (left right : KBytes) : (left ++ right).len = left.len + right.len := rfl

theorem slice_zero (bytes : KBytes) (offset : Nat) : bytes.slice offset 0 = .leaf 0 0 := by
  induction bytes generalizing offset with
  | leaf len value => simp [KBytes.slice, Nat.mod_one]
  | node len left right ihLeft ihRight =>
    by_cases h : offset ≤ left.len
    · simp [KBytes.slice, h, ihLeft]
    · have other : left.len ≤ offset := by omega
      simp [KBytes.slice, h, other, ihRight]

/-- Reslicing within the whole carrier preserves the exact structural window,
including at an empty child or at the end of a body. -/
theorem slice_full_slice (bytes : KBytes) (wf : bytes.wf = true) (offset width : Nat)
    (within : offset + width ≤ bytes.len) :
    (bytes.slice 0 bytes.len).slice offset width = bytes.slice offset width := by
  by_cases zero : width = 0
  · subst width
    simp only [slice_zero]
  induction bytes generalizing offset width with
  | leaf len value =>
    let leaf := KBytes.leaf len value
    change (leaf.slice 0 len).slice offset width = leaf.slice offset width
    have read := KBytes.readLE_slice leaf wf (off := 0) (w := len)
      (by change 0 + len ≤ len; omega) offset width
    have cutIn : offset + width ≤ (leaf.slice 0 len).len := by
      rw [KBytes.len_slice]
      exact within
    have leftRead : (leaf.slice 0 len).readLE offset width =
        some ((leaf.slice 0 len).read offset width) := ite_eq_left cutIn
    have rightRead : leaf.readLE offset width = some (leaf.read offset width) :=
      ite_eq_left within
    simp only [leftRead, Nat.zero_add, ite_eq_left (show offset + width ≤ len from within),
      rightRead] at read
    have result := Option.some.inj read
    exact congrArg (KBytes.leaf width) result
  | node len left right ihLeft ihRight =>
    simp only [KBytes.wf, Bool.and_eq_true, beq_iff_eq] at wf
    obtain ⟨⟨length, leftWf⟩, rightWf⟩ := wf
    change offset + width ≤ len at within
    subst len
    change ((KBytes.node (left.len + right.len) left right).slice 0
        (left.len + right.len)).slice offset width = _
    by_cases emptyRight : right.len = 0
    · have inLeft : offset + width ≤ left.len := by omega
      simp only [KBytes.slice, Nat.zero_add, emptyRight, Nat.add_zero, Nat.le_refl, ite_true,
        ite_eq_left inLeft]
      exact ihLeft leftWf offset width inLeft zero
    by_cases emptyLeft : left.len = 0
    · have inRight : offset + width ≤ right.len := by omega
      have positive : ¬ offset + width ≤ 0 := by omega
      simp only [KBytes.slice, Nat.zero_add, emptyLeft, Nat.not_le.2 (Nat.pos_of_ne_zero emptyRight),
        Nat.zero_le, positive, Nat.sub_zero, ite_true, ite_false]
      exact ihRight rightWf offset width inRight zero
    have full : (KBytes.node (left.len + right.len) left right).slice 0 (left.len + right.len) =
        .node (left.len + right.len) (left.slice 0 left.len) (right.slice 0 right.len) := by
      simp [KBytes.slice, show ¬ left.len + right.len ≤ left.len by omega,
        show ¬ left.len ≤ 0 by omega, show left.len + right.len - left.len = right.len by omega]
    rw [full]
    by_cases hLeft : offset + width ≤ left.len
    · simp only [KBytes.slice, KBytes.len_slice, ite_eq_left hLeft]
      exact ihLeft leftWf _ _ hLeft zero
    by_cases hRight : left.len ≤ offset
    · simp only [KBytes.slice, KBytes.len_slice, ite_eq_right hLeft, ite_eq_left hRight]
      exact ihRight rightWf _ _ (by omega) zero
    simp only [KBytes.slice, KBytes.len_slice, ite_eq_right hLeft, ite_eq_right hRight]
    rw [ihLeft leftWf _ _ (by omega) (by omega), ihRight rightWf _ _ (by omega) (by omega)]

/-- A byte tree occurs as an unmodified subtree of another tree. Its position
is the sum of the lengths of the preceding subtrees. -/
inductive Window (part : KBytes) : KBytes → Nat → Prop where
  | self : Window part part 0
  | left {front : KBytes} {offset : Nat} (previous : Window part front offset) (back : KBytes) :
      Window part (front ++ back) offset
  | right (front : KBytes) {back : KBytes} {offset : Nat} (previous : Window part back offset) :
      Window part (front ++ back) (front.len + offset)

theorem Window.extent {part whole : KBytes} {start : Nat} (atPart : Window part whole start) :
    start + part.len ≤ whole.len := by
  induction atPart with
  | self => simp
  | left _ _ ih => rw [append_length]; omega
  | right _ _ ih => rw [append_length]; omega

theorem Window.read {part whole : KBytes} {start : Nat} (atPart : Window part whole start)
    (offset width : Nat) (within : offset + width ≤ part.len) (positive : 0 < width) :
    whole.read (start + offset) width = part.read offset width := by
  induction atPart with
  | self => rw [Nat.zero_add]
  | left atChild back ih =>
    have extent := atChild.extent
    change (KBytes.node _ _ back).read _ _ = _
    rw [KBytes.read, ite_eq_left (by omega)]
    exact ih
  | @right front back childOffset atChild ih =>
    change (KBytes.node _ front _).read _ _ = _
    rw [KBytes.read, ite_eq_right (by omega), ite_eq_left (by omega)]
    rwa [show front.len + childOffset + offset - front.len = childOffset + offset by omega]

theorem Window.slice {part whole : KBytes} {start : Nat} (atPart : Window part whole start)
    (offset width : Nat) (within : offset + width ≤ part.len) :
    whole.slice (start + offset) width = part.slice offset width := by
  by_cases zero : width = 0
  · subst width
    simp only [slice_zero]
  induction atPart with
  | self => rw [Nat.zero_add]
  | left atChild back ih =>
    have extent := atChild.extent
    change (KBytes.node _ _ back).slice _ _ = _
    rw [KBytes.slice, ite_eq_left (by omega)]
    exact ih
  | @right front back childOffset atChild ih =>
    change (KBytes.node _ front _).slice _ _ = _
    rw [KBytes.slice, ite_eq_right (by omega), ite_eq_left (by omega)]
    rwa [show front.len + childOffset + offset - front.len = childOffset + offset by omega]

/-- A suffix follows successive right edges. It ends at the end of the
carrier, which is needed by the reader's exact EOS check. -/
inductive Suffix (tail : KBytes) : KBytes → Nat → Prop where
  | self : Suffix tail tail 0
  | right (front : KBytes) {rest : KBytes} {offset : Nat} (previous : Suffix tail rest offset) :
      Suffix tail (front ++ rest) (front.len + offset)

theorem Suffix.endOffset {tail whole : KBytes} {start : Nat} (atTail : Suffix tail whole start) :
    start + tail.len = whole.len := by
  induction atTail with
  | self => simp
  | right _ _ ih => rw [append_length]; omega

theorem Suffix.dropFrame {whole front rest : KBytes} {start : Nat}
    (atFrames : Suffix (front ++ rest) whole start) :
    Suffix rest whole (start + front.len) := by
  induction atFrames with
  | self => simpa using Suffix.right front (Suffix.self (tail := rest))
  | right prefixFrame previous ih => simpa only [Nat.add_assoc] using Suffix.right prefixFrame ih

theorem Suffix.frameWindow {whole front rest : KBytes} {start : Nat}
    (atFrames : Suffix (front ++ rest) whole start) :
    Window front whole start := by
  induction atFrames with
  | self => exact .left .self rest
  | right prefixFrame previous ih => exact .right prefixFrame ih

theorem Suffix.window {whole tail : KBytes} {start : Nat} (atTail : Suffix tail whole start) :
    Window tail whole start := by
  induction atTail with
  | self => exact .self
  | right front previous ih => exact .right front ih

end Silmaril.Proofs.Formats.Arrow.StreamWriter
